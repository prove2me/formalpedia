-- Prove2me | solution 1 for D1Bound5.exists_crossBlock_signed_scaled_error
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:59:57.934544+00:00
-- url     : https://prove2.me/submissions/15ecaeb4-ddf1-4a2d-aec8-5cfbdbb72ee6

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Int.GCD
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_RootMatrixSigns_Definitions
import Theorems.Thm_D1Bound5_signed_entry_crossBlock_scaled_error
import Theorems.Thm_D1Bound5_signed_entry_good_or_neg

section
open scoped BigOperators NumberField
open Module

namespace D1Bound5

/-- Simultaneous signs for an arbitrary rectangular three-by-three block.
All chosen entries stay in the original ring and retain the exact square
relations. No symmetry condition is imposed or needed. -/
theorem _root_.solution
    {R : Type*} [CommRing R] (f : R →+* ℂ)
    (a b : Fin 3 → R) (M : Fin 3 → Fin 3 → R)
    (hroot : ∀ i j, (M i j)^2 = a i*b j+1)
    (hlarge : ∀ i j, 9 ≤ ‖f (a i)*f (b j)‖) :
    ∃ (u v : Fin 3 → ℂ) (S : Fin 3 → Fin 3 → R),
      (∀ i, (u i)^2 = f (a i)) ∧
      (∀ j, (v j)^2 = f (b j)) ∧
      (∀ i j, (S i j)^2 = a i*b j+1) ∧
      (∀ i j, ‖(f (a i)*f (b j))*(u i*f (S i j)*v j)-
        (f (a i)*f (b j))^2-(1/2 : ℂ)*(f (a i)*f (b j))‖ < (2/15 : ℝ)) := by
  classical
  have hura (i : Fin 3) : ∃ z : ℂ, z^2 = f (a i) :=
    IsAlgClosed.exists_pow_nat_eq (f (a i)) (by decide : 0 < 2)
  have hur b' : ∃ z : ℂ, z^2 = f (b b') :=
    IsAlgClosed.exists_pow_nat_eq (f (b b')) (by decide : 0 < 2)
  choose u hu using hura
  choose v hv using hur
  have hex (i j : Fin 3) : ∃ s : R, s^2 = a i*b j+1 ∧
      SignedEntryGood f (a i) (b j) (u i) (v j) s := by
    rcases signed_entry_good_or_neg f (a i) (b j) (M i j) (u i) (v j)
      (hu i) (hv j) (hroot i j) (hlarge i j) with hg | hg
    · exact ⟨M i j, hroot i j, hg⟩
    · exact ⟨-M i j, by simpa only [neg_sq] using hroot i j, hg⟩
  choose S hS hgood using hex
  refine ⟨u, v, S, hu, hv, hS, ?_⟩
  intro i j
  exact signed_entry_crossBlock_scaled_error f (a i) (b j) (S i j)
    (u i) (v j) (hu i) (hv j) (hS i j) (hgood i j)









end D1Bound5
end
