-- Prove2me | solution 1 for D1Bound5.finiteN3_height_five_regions
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:27:40.956619+00:00
-- url     : https://prove2.me/submissions/1ff81b98-4d50-40e6-9842-c7ed1cab92ba

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.Convert
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_FiniteHomogeneousRatio_Definitions
import Definitions.Def_D1Bound5_FiniteHomogeneousTwo_Definitions
import Definitions.Def_D1Bound5_FiniteN3Height_Definitions
import Definitions.Def_D1Bound5_FiniteN3Matrix_Definitions
import Definitions.Def_D1Bound5_FiniteN3RatioHeight_Definitions
import Theorems.Thm_D1Bound5_finiteN3RatioWeights_nonneg
import Theorems.Thm_D1Bound5_finiteN3_root_coeff_decomposition
import Theorems.Thm_D1Bound5_finiteN3_root_coefficient_norm_le_ratio
import Theorems.Thm_D1Bound5_finitePolynomial_height_scalar
import Theorems.Thm_D1Bound5_finitePolynomial_two_columns_norm_le
import Theorems.Thm_D1Bound5_fiveRegionAnchorRatio_nonneg

section
noncomputable section

namespace D1Bound5



theorem finiteN3_ratio_root_decomposition {R : Type*} [CommRing R]
    (x y c : R) (i : Fin 3) (j : Fin 2) :
    ![finiteN3Left x y c i,finiteN3Right x y c i] j =
      ∑ ell : Fin 4, finiteN3RatioRootCoeff x y i j ell*c^(ell : ℕ) := by
  rw [finiteN3_root_coeff_decomposition]
  simp [finiteN3RatioRootCoeff,Fin.sum_univ_succ]
  <;> ring









set_option maxHeartbeats 4000000 in
/-- The five displayed coefficient constants are checked directly from the
actual integer coefficient vectors at their exact rational anchor ratios. -/
theorem finiteN3_five_region_height_slack (region : Fin 5) (i : Fin 3) :
    (101/100 : ℝ)*(∑ ell : Fin 4,
      finiteN3RatioWeights (fiveRegionAnchorRatio region) i ell/(1000 : ℝ)^(3-(ell : ℕ))) <
      fiveRegionN3Height region := by
  fin_cases region <;> fin_cases i <;>
    norm_num [finiteN3RatioWeights,fiveRegionAnchorRatio,fiveRegionN3Height,finiteHomogeneousRatioWeight,
      finiteN3Coeff0, finiteN3Coeff1, finiteN3Coeff2, finiteN3Coeff3,Fin.sum_univ_succ]

/-- Actual ratio-refined height for the constructed finite family. The
statement supplies no coefficient or height certificate: the integer rows
and all five rational table margins are proved above. -/
theorem _root_.solution (region : Fin 5) (x y c : ℂ)
    (hy : y ≠ 0) (hxy : ‖x‖ ≤ fiveRegionAnchorRatio region*‖y‖)
    (hYC : 1000 ≤ ‖y‖*‖c‖) (i : Fin 3) :
    (101/100 : ℝ)*(‖finiteN3Left x y c i‖+‖finiteN3Right x y c i‖) <
      fiveRegionN3Height region*‖y‖^7*‖c‖^3 := by
  let r := fiveRegionAnchorRatio region
  have hr : 0 ≤ r := fiveRegionAnchorRatio_nonneg region
  have hcoeff := finitePolynomial_two_columns_norm_le 3 4
    (finiteN3RatioRootCoeff x y i) (finiteN3RatioWeights r i) c ‖y‖
    (finiteN3_root_coefficient_norm_le_ratio x y r hr hxy i)
  have hleft := finiteN3_ratio_root_decomposition x y c i 0
  have hright := finiteN3_ratio_root_decomposition x y c i 1
  change finiteN3Left x y c i = _ at hleft
  change finiteN3Right x y c i = _ at hright
  rw [← hleft,← hright] at hcoeff
  have hscaled := mul_le_mul_of_nonneg_left hcoeff (show (0 : ℝ) ≤ 101/100 by norm_num)
  have hs := finitePolynomial_height_scalar 3 (finiteN3RatioWeights r i)
    (finiteN3RatioWeights_nonneg r hr i) (fiveRegionN3Height region) (‖y‖*‖c‖) hYC
    (finiteN3_five_region_height_slack region i)
  have hm := mul_lt_mul_of_pos_left hs (pow_pos (norm_pos_iff.mpr hy) 4)
  apply hscaled.trans_lt
  convert hm using 1 <;> simp only [mul_pow] <;> ring

end D1Bound5
end
