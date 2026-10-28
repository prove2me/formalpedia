-- Prove2me | solution 1 for D1Bound5.finiteP_height_scaled
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:42:40.673303+00:00
-- url     : https://prove2.me/submissions/639bd9ad-ee5d-4b4e-a092-195d000ec1e4

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_FinitePHeight_Definitions
import Theorems.Thm_D1Bound5_finiteP_root_columns_norm_le

section
open Finset

namespace D1Bound5

attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three

























theorem finiteP_height_scalar (C : ℝ) (hC : 200 ≤ C) :
    (101/100 : ℝ)*(492+2424*C+2352*C^2) < 2400*C^2 := by
  have hsq := mul_nonneg (sub_nonneg.mpr hC) (show 0 ≤ C by linarith)
  nlinarith only [hsq,hC]

theorem _root_.solution (a b s c : ℂ) (hA : 1 ≤ ‖a‖)
    (hAB : ‖a‖ ≤ ‖b‖) (hBS : ‖b‖ ≤ ‖s‖) (hC : 200 ≤ ‖c‖)
    (i : Fin 4) :
    (101/100 : ℝ)*(∑ j, ‖finitePRootColumn a b s c i j‖) <
      2400*max (‖b‖*‖s‖^3) (‖b‖^3*‖s‖^2)*‖c‖^2 := by
  have hB : 0 < ‖b‖ := by linarith
  have hS : 0 < ‖s‖ := lt_of_lt_of_le hB hBS
  have hH : 0 < max (‖b‖*‖s‖^3) (‖b‖^3*‖s‖^2) :=
    lt_of_lt_of_le (by positivity) (le_max_left _ _)
  have hb := mul_le_mul_of_nonneg_left
    (finiteP_root_columns_norm_le a b s c hA hAB hBS i) (by norm_num : (0:ℝ)≤101/100)
  have hs := mul_lt_mul_of_pos_left (finiteP_height_scalar ‖c‖ hC) hH
  nlinarith only [hb,hs]

end D1Bound5
end
