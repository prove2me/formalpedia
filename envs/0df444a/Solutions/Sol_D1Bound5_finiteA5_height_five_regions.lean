-- Prove2me | solution 1 for D1Bound5.finiteA5_height_five_regions
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:24:18.963865+00:00
-- url     : https://prove2.me/submissions/b5b2376e-dc2a-44df-80f5-229ccadae4b2

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
import Definitions.Def_D1Bound5_FiniteA5Coefficients_Definitions
import Definitions.Def_D1Bound5_FiniteA5Matrix_Definitions
import Definitions.Def_D1Bound5_FiniteA5RatioHeight_Definitions
import Definitions.Def_D1Bound5_FiniteHomogeneousRatio_Definitions
import Theorems.Thm_D1Bound5_finiteA5RatioWeights_nonneg
import Theorems.Thm_D1Bound5_finiteA5_five_region_height_slack
import Theorems.Thm_D1Bound5_finiteA5_root_coeff_decomposition
import Theorems.Thm_D1Bound5_finiteA5_root_coefficient_norm_le_ratio
import Theorems.Thm_D1Bound5_finitePolynomial_height_scalar
import Theorems.Thm_D1Bound5_finitePolynomial_two_columns_norm_le
import Theorems.Thm_D1Bound5_fiveRegionAnchorRatio_nonneg

section
noncomputable section

namespace D1Bound5











/-- Actual ratio-refined height for the constructed finite family. The
statement supplies no coefficient or height certificate: the integer rows
and all five rational table margins are proved above. -/
theorem _root_.solution (region : Fin 5) (x y c : ℂ)
    (hy : y ≠ 0) (hxy : ‖x‖ ≤ fiveRegionAnchorRatio region*‖y‖)
    (hYC : 1000 ≤ ‖y‖*‖c‖) (i : Fin 3) :
    (101/100 : ℝ)*(‖finiteA5Left x y c i‖+‖finiteA5Right x y c i‖) <
      fiveRegionA5Height region*‖y‖^12*‖c‖^5 := by
  let r := fiveRegionAnchorRatio region
  have hr : 0 ≤ r := fiveRegionAnchorRatio_nonneg region
  have hcoeff := finitePolynomial_two_columns_norm_le 5 7
    (finiteA5RootCoeff x y i) (finiteA5RatioWeights r i) c ‖y‖
    (finiteA5_root_coefficient_norm_le_ratio x y r hr hxy i)
  have hleft := finiteA5_root_coeff_decomposition x y c i 0
  have hright := finiteA5_root_coeff_decomposition x y c i 1
  change finiteA5Left x y c i = _ at hleft
  change finiteA5Right x y c i = _ at hright
  rw [← hleft,← hright] at hcoeff
  have hscaled := mul_le_mul_of_nonneg_left hcoeff (show (0 : ℝ) ≤ 101/100 by norm_num)
  have hs := finitePolynomial_height_scalar 5 (finiteA5RatioWeights r i)
    (finiteA5RatioWeights_nonneg r hr i) (fiveRegionA5Height region) (‖y‖*‖c‖) hYC
    (finiteA5_five_region_height_slack region i)
  have hm := mul_lt_mul_of_pos_left hs (pow_pos (norm_pos_iff.mpr hy) 7)
  apply hscaled.trans_lt
  convert hm using 1 <;> simp only [mul_pow] <;> ring

end D1Bound5
end
