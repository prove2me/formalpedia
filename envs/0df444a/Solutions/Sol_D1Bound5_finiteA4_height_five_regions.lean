-- Prove2me | solution 1 for D1Bound5.finiteA4_height_five_regions
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:27:33.800442+00:00
-- url     : https://prove2.me/submissions/c530efe4-bb3e-4117-ba4f-5ca28c202c18

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic
import Mathlib.Tactic.Convert
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_FiniteA4Coefficients_Definitions
import Definitions.Def_D1Bound5_FiniteA4Matrix_Definitions
import Definitions.Def_D1Bound5_FiniteA4RatioHeight_Definitions
import Definitions.Def_D1Bound5_FiniteHomogeneousRatio_Definitions
import Theorems.Thm_D1Bound5_finiteA4RatioWeights_nonneg
import Theorems.Thm_D1Bound5_finiteA4_root_coeff_decomposition
import Theorems.Thm_D1Bound5_finiteA4_root_coefficient_norm_le_ratio
import Theorems.Thm_D1Bound5_finitePolynomial_height_scalar
import Theorems.Thm_D1Bound5_finitePolynomial_two_columns_norm_le
import Theorems.Thm_D1Bound5_fiveRegionAnchorRatio_nonneg

section
noncomputable section

namespace D1Bound5









set_option maxHeartbeats 4000000 in
/-- The five displayed coefficient constants are checked directly from the
actual integer coefficient vectors at their exact rational anchor ratios. -/
theorem finiteA4_five_region_height_slack (region : Fin 5) (i : Fin 3) :
    (101/100 : ℝ)*(∑ ell : Fin 5,
      finiteA4RatioWeights (fiveRegionAnchorRatio region) i ell/(1000 : ℝ)^(4-(ell : ℕ))) <
      fiveRegionA4Height region := by
  fin_cases region <;> fin_cases i <;>
    norm_num [finiteA4RatioWeights,fiveRegionAnchorRatio,fiveRegionA4Height,finiteHomogeneousRatioWeight,
      finiteA4Coeff0, finiteA4Coeff1, finiteA4Coeff2, finiteA4Coeff3, finiteA4Coeff4,Fin.sum_univ_succ,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons]

/-- Actual ratio-refined height for the constructed finite family. The
statement supplies no coefficient or height certificate: the integer rows
and all five rational table margins are proved above. -/
theorem _root_.solution (region : Fin 5) (x y c : ℂ)
    (hy : y ≠ 0) (hxy : ‖x‖ ≤ fiveRegionAnchorRatio region*‖y‖)
    (hYC : 1000 ≤ ‖y‖*‖c‖) (i : Fin 3) :
    (101/100 : ℝ)*(‖finiteA4Left x y c i‖+‖finiteA4Right x y c i‖) <
      fiveRegionA4Height region*‖y‖^9*‖c‖^4 := by
  let r := fiveRegionAnchorRatio region
  have hr : 0 ≤ r := fiveRegionAnchorRatio_nonneg region
  have hcoeff := finitePolynomial_two_columns_norm_le 4 5
    (finiteA4RootCoeff x y i) (finiteA4RatioWeights r i) c ‖y‖
    (finiteA4_root_coefficient_norm_le_ratio x y r hr hxy i)
  have hleft := finiteA4_root_coeff_decomposition x y c i 0
  have hright := finiteA4_root_coeff_decomposition x y c i 1
  change finiteA4Left x y c i = _ at hleft
  change finiteA4Right x y c i = _ at hright
  rw [← hleft,← hright] at hcoeff
  have hscaled := mul_le_mul_of_nonneg_left hcoeff (show (0 : ℝ) ≤ 101/100 by norm_num)
  have hs := finitePolynomial_height_scalar 4 (finiteA4RatioWeights r i)
    (finiteA4RatioWeights_nonneg r hr i) (fiveRegionA4Height region) (‖y‖*‖c‖) hYC
    (finiteA4_five_region_height_slack region i)
  have hm := mul_lt_mul_of_pos_left hs (pow_pos (norm_pos_iff.mpr hy) 5)
  apply hscaled.trans_lt
  convert hm using 1 <;> simp only [mul_pow] <;> ring

end D1Bound5
end
