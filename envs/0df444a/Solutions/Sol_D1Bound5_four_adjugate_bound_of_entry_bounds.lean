-- Prove2me | solution 1 for D1Bound5.four_adjugate_bound_of_entry_bounds
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T01:24:03.358758+00:00
-- url     : https://prove2.me/submissions/57af24ef-9f47-4521-b192-3dd18b8bb08c

import Lean.Util.CollectAxioms
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_ProductFourNumericalClosure_Definitions
import Definitions.Def_D1Bound5_ReferenceMatrixSpectral_Definitions
import Definitions.Def_D1Bound5_RootMatrixOperatorBound_Definitions
import Theorems.Thm_D1Bound5_four_operator_norm_lt_of_entry_bounds
import Theorems.Thm_D1Bound5_halfOffDiagonalInverse_norm
import Theorems.Thm_D1Bound5_halfOffDiagonal_adjugate

section
open scoped Matrix.Norms.L2Operator
open Matrix

namespace D1Bound5







end D1Bound5


namespace D1Bound5

/-- The exact numerical margin in the four-by-four cofactor estimate. -/
theorem four_adjugate_numeric_margin :
    (3/8 : ℝ) + (23/1000 : ℝ) + 3*(197/10000 : ℝ) <
      productFourH * productFourS^2 := by
  unfold productFourH productFourS
  norm_num

/-- Once the diagonal/off-diagonal cofactor errors have their explicit
cubic estimates, the required L2 adjugate bound follows. This statement
exposes the two scalar inequalities as hypotheses. -/
theorem _root_.solution
    (F : Matrix (Fin 4) (Fin 4) ℂ)
    (hd : ∀ i, ‖(F.adjugate - halfOffDiagonal.adjugate) i i‖ <
      (23/1000 : ℝ))
    (hoff : ∀ i j, i ≠ j →
      ‖(F.adjugate - halfOffDiagonal.adjugate) i j‖ <
        (197/10000 : ℝ)) :
    ‖F.adjugate‖ < productFourH * productFourS^2 := by
  have href : ‖halfOffDiagonal.adjugate‖ = (3/8 : ℝ) := by
    rw [halfOffDiagonal_adjugate, norm_smul, halfOffDiagonalInverse_norm]
    norm_num
  have herr :=
    four_operator_norm_lt_of_entry_bounds
      (F.adjugate - halfOffDiagonal.adjugate)
      (23/1000 : ℝ) (197/10000 : ℝ)
      (by norm_num) (by norm_num) hd hoff
  have hdecomp : F.adjugate = halfOffDiagonal.adjugate +
      (F.adjugate - halfOffDiagonal.adjugate) := by abel
  calc
    ‖F.adjugate‖ =
      ‖halfOffDiagonal.adjugate +
        (F.adjugate - halfOffDiagonal.adjugate)‖ := congrArg norm hdecomp
    _ ≤ ‖halfOffDiagonal.adjugate‖ +
        ‖F.adjugate - halfOffDiagonal.adjugate‖ := norm_add_le _ _
    _ < (3/8 : ℝ) + (23/1000 : ℝ) + 3*(197/10000 : ℝ) := by
      rw [href]
      linarith only [herr]
    _ < productFourH * productFourS^2 := four_adjugate_numeric_margin

end D1Bound5

namespace D1Bound5



end D1Bound5
end
