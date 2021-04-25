; ****************** BEGIN INITIALIZATION FOR ACL2s MODE ****************** ;
; (Nothing to see here!  Your actual file is after this initialization code);
(make-event
 (er-progn
  (set-deferred-ttag-notes t state)
  (value '(value-triple :invisible))))

#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading the CCG book.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
(include-book "acl2s/ccg/ccg" :uncertified-okp nil :dir :system :ttags ((:ccg)) :load-compiled-file nil);v4.0 change

;Common base theory for all modes.
#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading ACL2s base theory book.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
(include-book "acl2s/base-theory" :dir :system :ttags :all)


#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading ACL2s customizations book.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
(include-book "acl2s/custom" :dir :system :ttags :all)

;; guard-checking-on is in *protected-system-state-globals* so any
;; changes are reverted back to what they were if you try setting this
;; with make-event. So, in order to avoid the use of progn! and trust
;; tags (which would not have been a big deal) in custom.lisp, I
;; decided to add this here.
;; 
;; How to check (f-get-global 'guard-checking-on state)
;; (acl2::set-guard-checking :nowarn)
(acl2::set-guard-checking :all)

;Settings common to all ACL2s modes
(acl2s-common-settings)
;(acl2::xdoc acl2s::defunc) ;; 3 seconds is too much time to spare -- commenting out [2015-02-01 Sun]

#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading ACL2s customizations book.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
(include-book "acl2s/acl2s-sigs" :dir :system :ttags :all)

#+acl2s-startup (er-progn (assign fmt-error-msg "Problem setting up ACL2s mode.") (value :invisible))

(acl2::xdoc acl2s::defunc) ; almost 3 seconds

; Non-events:
;(set-guard-checking :none)

(set-inhibit-warnings! "Invariant-risk" "theory")

(in-package "ACL2")
(redef+)
(defun print-ttag-note (val active-book-name include-bookp deferred-p state)
  (declare (xargs :stobjs state)
	   (ignore val active-book-name include-bookp deferred-p))
  state)

(defun print-deferred-ttag-notes-summary (state)
  (declare (xargs :stobjs state))
  state)

(defun notify-on-defttag (val active-book-name include-bookp state)
  (declare (xargs :stobjs state)
	   (ignore val active-book-name include-bookp))
  state)
(redef-)

(acl2::in-package "ACL2S")

; ******************* END INITIALIZATION FOR ACL2s MODE ******************* ;
;$ACL2s-SMode$;ACL2s
;; binary tree data structure
(defdata tree (oneof rational (list rational tree tree))) 

;; non-empty list of rationals data structure
(defdata ne-lor (oneof (cons rational nil)
                       (cons rational ne-lor)))


;; appends two non-empty lists of rationals together
(definec app2 (a :ne-lor b :ne-lor) :ne-lor
  (if (endp (rest a))
    (cons (first a) b)
    (cons (first a) (app2 (rest a) b))))

;; finds the maximum element of a tree
(definec tree-max (tr :tree) :rational
  (if (rationalp tr)
    tr
    (max (tree-max (cadr tr))
         (max (car tr)
              (tree-max (caddr tr))))))

;; finds the minimum element of a tree
(definec tree-min (tr :tree) :rational
  (if (rationalp tr)
    tr
    (min (tree-min (cadr tr))
         (min (car tr) 
              (tree-min (caddr tr))))))

;; predicate to determine whether a tree is ordered (is a binary search tree)
(definec ordered-treep (tr :tree) :bool
  (cond
   ((rationalp tr) t)
   ((consp tr) (and (ordered-treep (cadr tr))
                    (ordered-treep (caddr tr))
                    (<= (tree-max (cadr tr)) (car tr))
                    (>= (tree-min (caddr tr)) (car tr))))))

;; performs an inorder walk of the given tree, from the leftmost to the rightmost element
(definec inorder-walk (tr :tree) :ne-lor
  (if (rationalp tr) 
    (cons tr nil)
    (app2 (inorder-walk (cadr tr)) 
          (cons (car tr) (inorder-walk (caddr tr))))))

;; determines if a lllist of rationals is sorted from smallest to largest
(definec sorted-lorp (ls :ne-lor) :bool
  (cond 
   ((endp (cdr ls)) t)
   (t (and (<= (car ls) (cadr ls))
           (sorted-lorp (cdr ls))))))


;; =======================================================
;; NECESSARY THEOREMS FOR OUR LEMMA AND LEMMATA
;; =======================================================

;; the minimum of the left tree branch is less than the top node or right tree branch
(defthmd left-smallest-minimum
  (implies (and (treep tr)
                (consp tr)
                (ordered-treep tr))
           (<= (tree-min (cadr tr))
               (min (car tr)
                    (tree-min (caddr tr))))))

;; appending a non-empty list to another list does not change the first element
(defthmd car-l1-car-app2
  (implies (and (ne-lorp l1)
                (ne-lorp l2)
                (rationalp x))
           (equal (car l1) 
                  (car (app2 l1 (cons x l2))))))

;; the maximum of the left tree branch is less than the top node or right tree branch
(defthmd left-smallest-maximum
  (implies (and (treep tr)
                (consp tr)
                (ordered-treep tr))
           (<= (tree-max (cadr tr))
               (max (car tr)
                    (tree-max (caddr tr))))))

;; appending a list to the front of a non-empty list does not change the last element
(defthmd last-l1-last-app2-help
  (implies (and (ne-lorp l1)
                (ne-lorp l2)
                (ne-lorp l3)
                (equal (car (last l1))
                       (car (last l3))))
           (equal (car (last l1)) 
                  (car (last (app2 l2 l3))))))

;; adding elements to the front of a non-empty list does not change its last element
(defthmd last-l1-last-app2
  (implies (and (ne-lorp l1)
                (ne-lorp l2)
                (rationalp x))
           (equal (car (last l1)) 
                  (car (last (app2 l2 (cons x l1))))))
  :hints (("Goal" :use (:instance last-l1-last-app2-help
                        (l1 l1)
                        (l2 l2)
                        (l3 (cons x l1))))))


;; =======================================================
;; PROOF FOR THE FIRST LEMMA
;; =======================================================

;; the minimum of a tree is equal to the minimum of the left sub tree
(defthm equal-minimums
  (implies (and (treep tr)
                (consp tr)
                (ordered-treep tr))
           (equal (tree-min (cadr tr))
                  (tree-min tr)))
  :hints (("Goal" :use (left-smallest-minimum))))

;; the first element of the inorder walk of a tree is equal to the first element
;; of the in order walk of the left subtree
(defthm equal-first-elements
  (implies (and (treep tr)
                (consp tr)
                (ordered-treep tr))
           (equal (car (inorder-walk (cadr tr)))
                  (car (inorder-walk tr))))
  :hints (("Goal" :do-not-induct t
                  :use (:instance car-l1-car-app2 
                        (l1 (inorder-walk (cadr tr)))
                        (l2 (inorder-walk (caddr tr)))
                        (x (car tr))))))
                       
;; the minimum of a tree is the first element in an inorder walk
(defthm inorder-walk-starts-with-min
  (implies (and (treep tr)
                (ordered-treep tr))
           (equal (car (inorder-walk tr))
                  (tree-min tr)))
  :hints (("Goal" :induct (treep tr))))


;; =======================================================
;; PROOF FOR THE SECOND LEMMA
;; =======================================================

;; the maximum of the right tree branch is the maximum of the full tree
(defthm right-largest-maximum
  (implies (and (treep tr)
                (consp tr)
                (ordered-treep tr))
           (<= (car tr)
               (tree-max (caddr tr)))))

;; the maximum of a tree is equal to the maximum of the right sub tree
(defthm equal-maximums
  (implies (and (treep tr)
                (consp tr)
                (ordered-treep tr))
           (equal (tree-max (caddr tr))
                  (tree-max tr)))
  :hints (("Goal" :use (left-smallest-maximum))))

;; the last element of the inorder walk of a tree is equal to the last element
;; of the in order walk of the right subtree
(defthm equal-last-elements
  (implies (and (treep tr)
                (consp tr)
                (ordered-treep tr))
           (equal (car (last (inorder-walk (caddr tr))))
                  (car (last (inorder-walk tr)))))
  :hints (("Goal" :do-not-induct t
                  :use (:instance last-l1-last-app2
                        (l1 (inorder-walk (caddr tr)))
                        (l2 (inorder-walk (cadr tr)))
                        (x (car tr))))))

;; the miximum of a tree is the last element in an inorder walk
(defthm inorder-walk-ends-with-max
  (implies (and (treep tr)
                (ordered-treep tr))
           (equal (car (last (inorder-walk tr)))
                  (tree-max tr)))
  :hints (("Goal" :induct (treep tr))))


;; =======================================================
;; PROOF FOR THE THIRD LEMMA
;; =======================================================

;; appending two sorted lists for which the last of the first is less than
;; the first of the second produces a sorted list
(defthm app2-sorted
  (implies (and (ne-lorp l1)
                (ne-lorp l2)
                (sorted-lorp l1)
                (sorted-lorp l2)
                (<= (car (last l1)) (car l2)))
           (sorted-lorp (app2 l1 l2)))
  :hints (("Goal" :induct (ne-lorp l1))))


;; =======================================================
;; MAIN THEOREM TO PROVE
;; =======================================================

;; performing an inorder walk of an ordered tree creates a sorted list
(defthm sorted-inorder-walk 
  (implies (and (treep tr) (ordered-treep tr))
           (sorted-lorp (inorder-walk tr)))
  :hints (("Goal" :induct (treep tr))))

                  
                  
     
