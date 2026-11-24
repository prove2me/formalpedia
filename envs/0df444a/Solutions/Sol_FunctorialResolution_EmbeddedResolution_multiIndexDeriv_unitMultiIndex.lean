-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.multiIndexDeriv_unitMultiIndex
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:01:59.715468+00:00
-- url     : https://prove2.me/submissions/1dd25f51-5625-4d2e-bf54-4581fc28b39e

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_MultiIndexDerivation
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_unitMultiIndex_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] FunctorialResolution.EmbeddedResolution.unitMultiIndex_apply
section
namespace FunctorialResolution.EmbeddedResolution
section
variable {k R : Type*} [CommRing k] [CommRing R] [Algebra k R]
private theorem foldr_eq_of_eq_id_of_ne {A : Type*} :
    ∀ (n : ℕ) (F : Fin n → A → A) (i : Fin n) (f : A → A),
      (∀ j : Fin n, j ≠ i → ∀ y : A, F j y = y) → (∀ y : A, F i y = f y) →
      ∀ x : A, Fin.foldr n F x = f x := by
  intro n
  induction n with
  | zero =>
      intro F i
      exact i.elim0
  | succ m ih =>
      intro F i
      induction i using Fin.cases with
      | zero =>
          intro f hne heq x
          have hinner : Fin.foldr m (fun j : Fin m => F j.succ) x = x :=
            foldr_eq_self_of_forall_eq_self m (fun j : Fin m => F j.succ)
              (fun j y => hne j.succ (Fin.succ_ne_zero j) y) x
          rw [Fin.foldr_succ]
          show F 0 (Fin.foldr m (fun j : Fin m => F j.succ) x) = f x
          rw [hinner]
          exact heq x
      | succ j =>
          intro f hne heq x
          have hinner : Fin.foldr m (fun j' : Fin m => F j'.succ) x = f x :=
            ih (fun j' : Fin m => F j'.succ) j f
              (fun j' hj' y => hne j'.succ (fun hc => hj' (Fin.succ_injective m hc)) y)
              (fun y => heq y) x
          rw [Fin.foldr_succ]
          show F 0 (Fin.foldr m (fun j' : Fin m => F j'.succ) x) = f x
          rw [hinner]
          exact hne 0 (Ne.symm (Fin.succ_ne_zero j)) (f x)
end
end FunctorialResolution.EmbeddedResolution
end

set_option autoImplicit false
open FunctorialResolution FunctorialResolution.EmbeddedResolution
variable {k R : Type*} [CommRing k] [CommRing R] [Algebra k R]
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution {h : ℕ} (D : Fin h → Derivation k R R) (i : Fin h) (x : R) :
    multiIndexDeriv D (unitMultiIndex i) x = D i x := by
  show Fin.foldr h (fun j y => (⇑(D j))^[unitMultiIndex i j] y) x = D i x
  refine foldr_eq_of_eq_id_of_ne h (fun j y => (⇑(D j))^[unitMultiIndex i j] y) i
    (⇑(D i)) ?_ ?_ x
  · intro j hj y
    simp [unitMultiIndex, hj]
  · intro y
    simp [unitMultiIndex]
end FunctorialResolution.EmbeddedResolution
