module AssociationList where

open import Relation.Binary.PropositionalEquality renaming ([_] to [_]in)
open import Relation.Binary hiding (REL; module Tri) renaming (Tri to Trich)

open import Pivotal
open Sg

module OrderedList {A : Set}{P : Set}(p : A -> P)(L : REL P) where

  inj : A -> <$ P $>D
  inj a = tb (p a)

  data OList (lu : <$ P $>D * <$ P $>D) : Set where
    nil   :  { _ : <$ L $>F lu} → OList lu
    cons  :  (a : A) →
             { _ : <$ L $>F (fst lu / inj a) } → OList (inj a / snd lu) → OList lu 

  -- Instance arguments often let us omit proofs in expressions.
  -- They are quite slow though, so probably overkill.
  nil' : {lu : <$ P $>D * <$ P $>D} {{ _ : <$ L $>F lu}} → OList lu
  nil' = nil {_} { ! }

  cons' : {lu : <$ P $>D * <$ P $>D} (a : A) → {{ _ : <$ L $>F (fst lu / inj a) }} → OList (inj a / snd lu) → OList lu 
  cons' a = cons a { ! }

module Test where
  open OrderedList

  -- The relation is defined by recusion rather than as an inductive
  -- family because Agda can fill in inhabitants of One by
  -- eta-expansion.

  Lt : REL Nat
  Lt (x / y) = x <' y where
    _<'_ : Nat → Nat → Set
    ze   <' ze   = Zero
    ze   <' su y = One
    su x <' ze   = Zero
    su x <' su y = x <' y

  OL = OList id Lt

  -- Ensures uniquess and ordering
  xs : Zero → OL (bot / top)
  xs NOSUCHPROOF = cons 2 (cons 2 {NOSUCHPROOF} nil)

  ys : Zero → OL (bot / top)
  ys NOSUCHPROOF = cons 3 (cons 2 {NOSUCHPROOF} nil)

data Tri {A : Set} (P : REL A) (xy : A * A) : Set where 
  x<y : P xy → Tri P xy
  x≡y : fst xy ≡ snd xy → Tri P xy
  y<x : P (snd xy / fst xy) → Tri P xy

uncurry : ∀ {A B}{c}{C : Set c} → (A → B → C) → (A * B → C)
uncurry f (a / b) = f a b

record ExtSTO (A : Set) : Set₁  where
  field
    _<_ : A → A → Set
    isSTO : IsStrictTotalOrder _≡_ _<_ 

  open IsStrictTotalOrder isSTO

  dec< : ∀ x → Tri (uncurry _<_) x
  dec< (x / y) with compare x y 
  dec< (x / y) | tri< a ¬b ¬c = x<y a
  dec< (x / y) | tri≈ ¬a b ¬c = x≡y b
  dec< (x / y) | tri> ¬a ¬b c = y<x c

module AssocList (K : Set) (V : Set) (O : ExtSTO K) where

  open ExtSTO O

  Pred : REL K
  Pred = uncurry _<_

  open OrderedList {A = K * V} fst (uncurry _<_)

  List = OList (bot / top)

  insert : ∀ v -> [ <$ Pred $>II >> OList >> OList ]
  insert v (k / _  / _) nil                 = cons' (k / v) nil'
  insert v (k / _  / _) (cons (kp / vp) xs) with dec< (k / kp) 
  insert v (k / _  / _) (cons (kp / vp) xs) | x<y _    = cons' (k / v) (cons' (kp / vp) xs)
  insert v (k / lk / _) (cons (.k / vp) xs) | x≡y refl = cons (k / v) {lk} xs
  insert v (k / _  / _) (cons (kp / vp) xs) | y<x _    = cons' (kp / vp) (insert v (k / ! / !) xs)

  lookup : K → ∀ {ul} → (xs : OList ul) → Maybe V
  lookup k nil                = no
  lookup k (cons (k' / v) xs) with dec< (k / k')
  lookup k (cons (k' / v) xs) | x<y x = no
  lookup k (cons (k' / v) xs) | x≡y x = yes v
  lookup k (cons (k' / v) xs) | y<x x = lookup k xs

  Entry = <$ Pred $>II
  
  key : ∀ {ul} -> Entry ul -> K
  key (k / _ / _) = k
  
 
  lemma : ∀ {lu} k {v kl} (xs : OList (_ / snd lu)) -> lookup k (cons {lu} (k / v) {kl} xs) ≡ yes v
  lemma k xs with dec< (k / k)
  ... | z = {!!}

  proof : ∀ {ul} {v} (e : Entry ul) (xs : OList ul) -> lookup (key {ul} e) (insert v e xs) ≡ yes v
  proof {ul} (k / lk / ku) nil = lemma {ul} k {kl = !} nil'
  proof {ul} (k / lk / ku) (cons (k' / _) xs) with dec< (k / k') | inspect dec< (k / k') 
  proof {ul} (k / lk / ku) (cons (k' / v') xs) | x<y x    | _ = lemma {ul} k {kl = lk} (cons' (k' / v') xs)
  proof {ul} (k / lk / ku) (cons (.k / v') xs) | x≡y refl | _ = lemma {ul} k {kl = lk} xs
  proof      (k / lk / ku) (cons (k' / v') xs) | y<x x    | [ eq ]in rewrite eq = proof (k / x / ku) xs
