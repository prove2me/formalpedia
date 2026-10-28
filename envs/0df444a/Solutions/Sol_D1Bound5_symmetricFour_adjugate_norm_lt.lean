-- Prove2me | solution 1 for D1Bound5.symmetricFour_adjugate_norm_lt
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:37:44.044412+00:00
-- url     : https://prove2.me/submissions/2d2db0aa-2886-4365-a8ce-8d91ea7e896d

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
import Definitions.Def_D1Bound5_AdjugateCoverage_Definitions
import Definitions.Def_D1Bound5_ProductFourNumericalClosure_Definitions
import Definitions.Def_D1Bound5_RootMatrixOperatorBound_Definitions
import Theorems.Thm_D1Bound5_four_adjugate_bound_of_entry_bounds
import Theorems.Thm_D1Bound5_halfOffDiagonal_adjugate_apply
import Theorems.Thm_D1Bound5_nearHalf_offDiagonal_cofactor_bound
import Theorems.Thm_D1Bound5_nearHalf_triple_cofactor_bound
import Theorems.Thm_D1Bound5_symmetricFour_adjugate_formula

section
open scoped Matrix.Norms.L2Operator
open Matrix

namespace D1Bound5







/-- Unconditional adjugate operator-norm estimate for all six
independently chosen entries satisfying the previously proved near-half bounds. -/
theorem _root_.solution (x y z u v w : ℂ)
    (hx : ‖x-(1/2 : ℂ)‖ < (128/8649 : ℝ))
    (hy : ‖y-(1/2 : ℂ)‖ < (128/8649 : ℝ))
    (hz : ‖z-(1/2 : ℂ)‖ < (128/8649 : ℝ))
    (hu : ‖u-(1/2 : ℂ)‖ < (128/8649 : ℝ))
    (hv : ‖v-(1/2 : ℂ)‖ < (128/8649 : ℝ))
    (hw : ‖w-(1/2 : ℂ)‖ < (128/8649 : ℝ)) :
    ‖(symmetricFour x y z u v w).adjugate‖ <
      productFourH * productFourS^2 := by
  let F := symmetricFour x y z u v w
  have hAdj : F.adjugate = symmetricFourAdj x y z u v w :=
    symmetricFour_adjugate_formula x y z u v w
  have h00 := nearHalf_triple_cofactor_bound u v w hu hv hw
  have h11 := nearHalf_triple_cofactor_bound y z w hy hz hw
  have h22 := nearHalf_triple_cofactor_bound x z v hx hz hv
  have h33 := nearHalf_triple_cofactor_bound x y u hx hy hu
  have h01 := nearHalf_offDiagonal_cofactor_bound x y z u v w hx hy hz hu hv hw
  have h02 := nearHalf_offDiagonal_cofactor_bound y x z u w v hy hx hz hu hw hv
  have h03 := nearHalf_offDiagonal_cofactor_bound z x y v w u hz hx hy hv hw hu
  have h12 := nearHalf_offDiagonal_cofactor_bound u x y v w z hu hx hy hv hw hz
  have h13 := nearHalf_offDiagonal_cofactor_bound v z x w u y hv hz hx hw hu hy
  have h23 := nearHalf_offDiagonal_cofactor_bound w z y v u x hw hz hy hv hu hx
  apply four_adjugate_bound_of_entry_bounds F
  · intro i
    fin_cases i
    · simpa [Matrix.sub_apply, hAdj, symmetricFourAdj,
             halfOffDiagonal_adjugate_apply, sub_neg_eq_add, neg_div] using h00
    · simpa [Matrix.sub_apply, hAdj, symmetricFourAdj,
             halfOffDiagonal_adjugate_apply, sub_neg_eq_add, neg_div] using h11
    · simpa [Matrix.sub_apply, hAdj, symmetricFourAdj,
             halfOffDiagonal_adjugate_apply, sub_neg_eq_add, neg_div] using h22
    · simpa [Matrix.sub_apply, hAdj, symmetricFourAdj,
             halfOffDiagonal_adjugate_apply, sub_neg_eq_add, neg_div] using h33
  · intro i j hij
    fin_cases i <;> fin_cases j <;> try simp at hij
    all_goals first
      | simpa [Matrix.sub_apply, hAdj, symmetricFourAdj,
               halfOffDiagonal_adjugate_apply, sub_neg_eq_add, neg_div] using h01
      | simpa [Matrix.sub_apply, hAdj, symmetricFourAdj,
               halfOffDiagonal_adjugate_apply, sub_neg_eq_add, neg_div] using h02
      | simpa [Matrix.sub_apply, hAdj, symmetricFourAdj,
               halfOffDiagonal_adjugate_apply, sub_neg_eq_add, neg_div] using h03
      | simpa [Matrix.sub_apply, hAdj, symmetricFourAdj,
               halfOffDiagonal_adjugate_apply, sub_neg_eq_add, neg_div] using h12
      | simpa [Matrix.sub_apply, hAdj, symmetricFourAdj,
               halfOffDiagonal_adjugate_apply, sub_neg_eq_add, neg_div] using h13
      | simpa [Matrix.sub_apply, hAdj, symmetricFourAdj,
               halfOffDiagonal_adjugate_apply, sub_neg_eq_add, neg_div] using h23



end D1Bound5
end
