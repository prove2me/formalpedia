-- Prove2me | solution 1 for D1Bound5.mixed_four_det_ne_zero_of_entry_bounds
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:01:00.908078+00:00
-- url     : https://prove2.me/submissions/607f08ac-fb34-4319-aaa1-bf50b1fbbab7

import Lean.Util.CollectAxioms
import Mathlib.Algebra.CharP.Frobenius
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
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
import Definitions.Def_D1Bound5_ReferenceMatrixSpectral_Definitions
import Definitions.Def_D1Bound5_RootMatrixOperatorBound_Definitions
import Theorems.Thm_D1Bound5_halfOffDiagonalInverse_norm
import Theorems.Thm_D1Bound5_mixedFour_operator_norm_le
import Theorems.Thm_D1Bound5_reference_perturbed_det_ne_zero

section
open scoped NumberField Matrix.Norms.L2Operator BigOperators
open Matrix Module

namespace D1Bound5

/-- Invertibility of a mixed normalized error matrix from its entrywise bounds. -/
theorem _root_.solution
    (F : Matrix (Fin 4) (Fin 4) ℂ)
    (hdiag : ∀ i, F i i = 0)
    (hfirst : ∀ i j, i ≠ j → i = 0 ∨ j = 0 →
      ‖F i j - (1/2 : ℂ)‖ < (1/18 : ℝ))
    (hlater : ∀ i j, i ≠ j → ¬(i = 0 ∨ j = 0) →
      ‖F i j - (1/2 : ℂ)‖ < (1/64 : ℝ)) :
    F.det ≠ 0 := by
  have hd : ∀ i, (F - halfOffDiagonal) i i = 0 := by
    intro i
    simpa [Matrix.sub_apply, halfOffDiagonal, hdiag i]
  have hf : ∀ i j, i ≠ j → i = 0 ∨ j = 0 →
      ‖(F - halfOffDiagonal) i j‖ < (1/18 : ℝ) := by
    intro i j hij hz
    simpa [Matrix.sub_apply, halfOffDiagonal, hij] using hfirst i j hij hz
  have hl : ∀ i j, i ≠ j → ¬(i = 0 ∨ j = 0) →
      ‖(F - halfOffDiagonal) i j‖ < (1/64 : ℝ) := by
    intro i j hij hz
    simpa [Matrix.sub_apply, halfOffDiagonal, hij] using hlater i j hij hz
  have hnear : ‖F - halfOffDiagonal‖ ≤ (11/96 : ℝ) :=
    mixedFour_operator_norm_le (F - halfOffDiagonal) hd hf hl
  have hsmall :
      ‖halfOffDiagonalInverse * (F - halfOffDiagonal)‖ < 1 := by
    calc
      ‖halfOffDiagonalInverse * (F - halfOffDiagonal)‖
          ≤ ‖halfOffDiagonalInverse‖ * ‖F - halfOffDiagonal‖ :=
            Matrix.l2_opNorm_mul _ _
      _ = 2 * ‖F - halfOffDiagonal‖ := by rw [halfOffDiagonalInverse_norm]
      _ ≤ 2 * (11/96 : ℝ) :=
        mul_le_mul_of_nonneg_left hnear (by norm_num)
      _ < 1 := by norm_num
  exact reference_perturbed_det_ne_zero F hsmall















end D1Bound5
end
