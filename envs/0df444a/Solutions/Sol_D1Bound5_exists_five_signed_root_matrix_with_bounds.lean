-- Prove2me | solution 1 for D1Bound5.exists_five_signed_root_matrix_with_bounds
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:39:23.543501+00:00
-- url     : https://prove2.me/submissions/2cfaadd2-41b9-47c0-a8f0-99c49a1e8fb3

import Lean.Util.CollectAxioms
import Mathlib.Algebra.CharP.Frobenius
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_DeterminantNormalization_Definitions
import Definitions.Def_D1Bound5_MixedRootMatrixSigns_Definitions
import Definitions.Def_D1Bound5_ProductFiveCompatibleSigns_Definitions
import Definitions.Def_D1Bound5_ProductFiveMatrixBridge_Definitions
import Theorems.Thm_D1Bound5_exists_five_signed_root_matrix
import Theorems.Thm_D1Bound5_fiveSignedEntryGood_last_column
import Theorems.Thm_D1Bound5_fiveSignedEntryGood_prefix
import Theorems.Thm_D1Bound5_five_prefix_det_upper_of_mixed_signed_entries

section
namespace D1Bound5















/-- Choose all five complex square roots and all ten original-ring signs.
The prefix determinant and last-column bounds use a single witness S. -/
theorem _root_.solution
    {R : Type*} [CommRing R] (f : R →+* ℂ)
    (a : Fin 5 → R) (M : Matrix (Fin 5) (Fin 5) R)
    (hdiag : ∀ i, M i i = a i)
    (hsymm : ∀ i j, M i j = M j i)
    (hroot : ∀ i j, i ≠ j → (M i j)^2 = a i * a j + 1)
    (hfirst : ∀ i j, i ≠ j → 3 ≤ ‖f (a i)*f (a j)‖)
    (hlater : ∀ i j, i ≠ j → ¬(i = 0 ∨ j = 0) →
      9 ≤ ‖f (a i)*f (a j)‖)
    (hlast : ∀ i j, i ≠ j → i = 4 ∨ j = 4 →
      54 ≤ ‖f (a i)*f (a j)‖) :
    ∃ (u : Fin 5 → ℂ) (S : Matrix (Fin 5) (Fin 5) R),
      (∀ i, (u i)^2 = f (a i)) ∧
      (∀ i, S i i = a i) ∧
      (∀ i j, S i j = S j i) ∧
      (∀ i j, i ≠ j → S i j = M i j ∨ S i j = -M i j) ∧
      (∀ i j, i ≠ j → (S i j)^2 = a i*a j+1) ∧
      (∀ i j, i ≠ j → FiveSignedEntryGood f a u i j (S i j)) ∧
      ‖(fivePrefixError (normalizedRootError (fun i => f (a i)) u
        (fun i j => f (S i j)))).det‖ < (33/128 : ℝ) ∧
      (∀ i : Fin 4,
        ‖fiveLastError (normalizedRootError (fun k => f (a k)) u
          (fun k l => f (S k l))) i - (1/2 : ℂ)‖ < (1/400 : ℝ)) := by
  classical
  have hr (i : Fin 5) : ∃ z : ℂ, z^2 = f (a i) :=
    IsAlgClosed.exists_pow_nat_eq (f (a i)) (by decide : 0 < 2)
  let u : Fin 5 → ℂ := fun i => Classical.choose (hr i)
  have hu (i : Fin 5) : (u i)^2 = f (a i) := Classical.choose_spec (hr i)
  obtain ⟨S, hd, hs, hsign, hsq, hg⟩ :=
    exists_five_signed_root_matrix f a u M hu hdiag hsymm hroot hfirst hlater hlast
  have hp := fiveSignedEntryGood_prefix f a u S hg
  have hdet := five_prefix_det_upper_of_mixed_signed_entries f a u S hu hd hs hp
  have hcol := fiveSignedEntryGood_last_column f a u S hg
  exact ⟨u, S, hu, hd, hs, hsign, hsq, hg, hdet, fun i => (hcol i).2⟩

open scoped NumberField
open Module








end D1Bound5
end
