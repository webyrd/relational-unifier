;;; Beginning of a miniKanren implementation of relational unification,
;;; based on the Scheme implementation of unification.
;;; Currently this code only contains a relational version of 'walk'.
;;;
;;; The relational 'walk' code was translated, with description,
;;; during the 5th miniKanren Hangout:
;;;
;;; https://www.youtube.com/watch?v=VSpq3qK9L88

(load "mk.scm")
;;; Using the version of miniKanren with absento and numbero constraints
;;; from:
;;; https://github.com/webyrd/2012-scheme-workshop-quines-paper-code/blob/master/appendixD.scm
(load "testcheck.scm")


;;; terms in our language:
;;; 1. Scheme numbers:  5, 137, etc.
;;; 2. tagged variables:  `(var ,x) for some x
;;; 3. (non-tagged variable) pairs:  (5 . 6), (() . (5 . ()))
;;; 4. empty list: ()

;;; Substitution: ((x y) (5 6))


(define make-var (lambda (x) `(var ,x)))

(define var?o
  (lambda (t)
    (fresh (x)
      (== (make-var x) t))))

(define not-var?o
  (lambda (t)
    (conde
      [(== '() t)]
      [(numbero t)]
      [(fresh (a d)
         (== `(,a . ,d) t)
         (=/= 'var a))])))

(define lookupo
  (lambda (x S t)
    (fresh (y y-rest t^ t-rest)
      (== `((,y . ,y-rest) (,t^ . ,t-rest)) S)
      (conde
        [(== y x) (== t^ t)]
        [(=/= y x) (lookupo x `(,y-rest ,t-rest) t)]))))

(define walko
  (lambda (u S u^)
    (conde
      [(var?o u)
       (fresh (t)
         (lookupo u S t)
         (walko t S u^))]      
      [(not-var?o u) (== u^ u)]
      [(fresh (y* t*)
         (var?o u)
         (== `(,y* ,t*) S)
         (absento u y*)
         (== u^ u))])))

(test-check "walko-1"
  (run 10 (q)
    (fresh (t S t^)
      (walko t S t^)
      (== `(,t ,S ,t^) q)))
  '((() _.0 ())
    ((_.0 _.1 _.0) (num _.0))
    (((_.0 . _.1) _.2 (_.0 . _.1)) (=/= ((_.0 var))))
    ((var _.0) (((var _.0) . _.1) (() . _.2)) ())
    (((var _.0) (((var _.0) . _.1) (_.2 . _.3)) _.2) (num _.2))
    (((var _.0)
      (((var _.0) . _.1) ((_.2 . _.3) . _.4))
      (_.2 . _.3))
     (=/= ((_.2 var))))
    (((var _.0) ((_.1 (var _.0) . _.2) (_.3 () . _.4)) ())
     (=/= ((_.1 (var _.0)))))
    (((var _.0) ((_.1 (var _.0) . _.2) (_.3 _.4 . _.5)) _.4)
     (=/= ((_.1 (var _.0))))
     (num _.4))
    (((var _.0)
      ((_.1 (var _.0) . _.2) (_.3 (_.4 . _.5) . _.6))
      (_.4 . _.5))
     (=/= ((_.1 (var _.0))) ((_.4 var))))
    (((var _.0)
      ((_.1 _.2 (var _.0) . _.3) (_.4 _.5 () . _.6))
      ())
     (=/= ((_.1 (var _.0))) ((_.2 (var _.0)))))))

(test-check "walko-2"
  (run* (q)
    (fresh (v1 S)
      (== (make-var 'x) v1)
      (== `((,v1) (5)) S)
      (walko v1 S q)))
  '(5))

#!eof

;;; Original Scheme code from 

(define-syntax var
  (syntax-rules ()
    ((_ x) (vector x))))

(define-syntax var?
  (syntax-rules ()
    ((_ x) (vector? x))))

(define-syntax rhs
  (syntax-rules ()
    ((_ x) (cdr x))))

(define-syntax lhs
  (syntax-rules ()
    ((_ x) (car x))))

(define unify
  (lambda (u v s)
    (let ((u (walk u s))
          (v (walk v s)))
      (cond
        ((eq? u v) s)
        ((var? u) (ext-s-check u v s))
        ((var? v) (ext-s-check v u s))
        ((and (pair? u) (pair? v))
         (let ((s (unify
                    (car u) (car v) s)))
           (and s (unify
                    (cdr u) (cdr v) s))))
        ((equal? u v) s)
        (else #f)))))

(define ext-s-check
  (lambda (x v s)
    (cond
      ((occurs-check x v s) #f)
      (else (ext-s x v s)))))

(define ext-s
  (lambda (x v s)
    (cons `(,x . ,v) s)))

(define occurs-check
  (lambda (x v s)
    (let ((v (walk v s)))
      (cond
        ((var? v) (eq? v x))
        ((pair? v)
         (or
           (occurs-check x (car v) s)
           (occurs-check x (cdr v) s)))
        (else #f)))))

(define walk
  (lambda (u S)
    (cond
      ((and (var? u) (assq u S)) =>
       (lambda (pr) (walk (rhs pr) S)))
      (else u))))
