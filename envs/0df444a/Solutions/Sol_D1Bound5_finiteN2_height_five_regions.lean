-- Prove2me | solution 1 for D1Bound5.finiteN2_height_five_regions
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:24:20.566997+00:00
-- url     : https://prove2.me/submissions/7df53636-57ac-4169-81f7-029860d21980

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
import Definitions.Def_D1Bound5_FiniteN2Height_Definitions
import Definitions.Def_D1Bound5_FiniteN2Matrix_Definitions
import Definitions.Def_D1Bound5_FiniteN2RatioHeight_Definitions
import Theorems.Thm_D1Bound5_finiteHomogeneousRatioWeight_nonneg
import Theorems.Thm_D1Bound5_finiteN2_root_coeff_decomposition
import Theorems.Thm_D1Bound5_finiteN2_root_coefficient_norm_le_ratio
import Theorems.Thm_D1Bound5_finitePolynomial_height_scalar
import Theorems.Thm_D1Bound5_finitePolynomial_two_columns_norm_le
import Theorems.Thm_D1Bound5_fiveRegionAnchorRatio_nonneg

section
noncomputable section

namespace D1Bound5



theorem finiteN2_ratio_root_decomposition {R : Type*} [CommRing R]
    (x y c : R) (i : Fin 3) (j : Fin 2) :
    ![finiteN2Left x y c i,finiteN2Right x y c i] j =
      ∑ ell : Fin 3, finiteN2RatioRootCoeff x y i j ell*c^(ell : ℕ) := by
  rw [finiteN2_root_coeff_decomposition]
  simp [finiteN2RatioRootCoeff,Fin.sum_univ_succ]
  <;> ring





theorem finiteN2RatioWeights_nonneg (r : ℝ) (hr : 0 ≤ r) (i : Fin 3) (ell : Fin 3) :
    0 ≤ finiteN2RatioWeights r i ell := by
  fin_cases ell
  · exact add_nonneg (finiteHomogeneousRatioWeight_nonneg 2 _ r hr)
      (finiteHomogeneousRatioWeight_nonneg 2 _ r hr)
  · exact add_nonneg (finiteHomogeneousRatioWeight_nonneg 3 _ r hr)
      (finiteHomogeneousRatioWeight_nonneg 3 _ r hr)
  · exact add_nonneg (finiteHomogeneousRatioWeight_nonneg 4 _ r hr)
      (finiteHomogeneousRatioWeight_nonneg 4 _ r hr)



set_option maxHeartbeats 4000000 in
/-- The five displayed coefficient constants are checked directly from the
actual integer coefficient vectors at their exact rational anchor ratios. -/
theorem finiteN2_five_region_height_slack (region : Fin 5) (i : Fin 3) :
    (101/100 : ℝ)*(∑ ell : Fin 3,
      finiteN2RatioWeights (fiveRegionAnchorRatio region) i ell/(1000 : ℝ)^(2-(ell : ℕ))) <
      fiveRegionN2Height region := by
  fin_cases region <;> fin_cases i <;>
    norm_num [finiteN2RatioWeights,fiveRegionAnchorRatio,fiveRegionN2Height,finiteHomogeneousRatioWeight,
      finiteN2Coeff0, finiteN2Coeff1, finiteN2Coeff2,Fin.sum_univ_succ]

/-- Actual ratio-refined height for the constructed finite family. The
statement supplies no coefficient or height certificate: the integer rows
and all five rational table margins are proved above. -/
theorem _root_.solution (region : Fin 5) (x y c : ℂ)
    (hy : y ≠ 0) (hxy : ‖x‖ ≤ fiveRegionAnchorRatio region*‖y‖)
    (hYC : 1000 ≤ ‖y‖*‖c‖) (i : Fin 3) :
    (101/100 : ℝ)*(‖finiteN2Left x y c i‖+‖finiteN2Right x y c i‖) <
      fiveRegionN2Height region*‖y‖^4*‖c‖^2 := by
  let r := fiveRegionAnchorRatio region
  have hr : 0 ≤ r := fiveRegionAnchorRatio_nonneg region
  have hcoeff := finitePolynomial_two_columns_norm_le 2 2
    (finiteN2RatioRootCoeff x y i) (finiteN2RatioWeights r i) c ‖y‖
    (finiteN2_root_coefficient_norm_le_ratio x y r hr hxy i)
  have hleft := finiteN2_ratio_root_decomposition x y c i 0
  have hright := finiteN2_ratio_root_decomposition x y c i 1
  change finiteN2Left x y c i = _ at hleft
  change finiteN2Right x y c i = _ at hright
  rw [← hleft,← hright] at hcoeff
  have hscaled := mul_le_mul_of_nonneg_left hcoeff (show (0 : ℝ) ≤ 101/100 by norm_num)
  have hs := finitePolynomial_height_scalar 2 (finiteN2RatioWeights r i)
    (finiteN2RatioWeights_nonneg r hr i) (fiveRegionN2Height region) (‖y‖*‖c‖) hYC
    (finiteN2_five_region_height_slack region i)
  have hm := mul_lt_mul_of_pos_left hs (pow_pos (norm_pos_iff.mpr hy) 2)
  apply hscaled.trans_lt
  convert hm using 1 <;> simp only [mul_pow] <;> ring

end D1Bound5
end
