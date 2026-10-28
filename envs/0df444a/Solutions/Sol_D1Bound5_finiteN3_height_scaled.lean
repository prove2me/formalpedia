-- Prove2me | solution 1 for D1Bound5.finiteN3_height_scaled
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:00:26.436665+00:00
-- url     : https://prove2.me/submissions/512d0a8e-d756-4a51-94e6-8b02cefc3b87

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
import Definitions.Def_D1Bound5_FiniteN3Matrix_Definitions
import Theorems.Thm_D1Bound5_finiteN3_root_columns_norm_le

section
namespace D1Bound5


















theorem finiteN3_height_scalar (T : ℝ) (hT : 1000 ≤ T) :
    (101/100 : ℝ)*(342+2352*T+5792*T^2+4096*T^3) < 4143*T^3 := by
  have hT0 : 0 ≤ T := by linarith only [hT]
  have h1 := mul_nonneg (sub_nonneg.mpr hT) hT0
  have h2 := mul_nonneg (sub_nonneg.mpr hT) (sq_nonneg T)
  nlinarith only [hT,h1,h2]

/-- The actual finite N3 coefficient height with the manuscript's4143. -/
theorem _root_.solution (x y c : ℂ) (hy : y ≠ 0)
    (hxy : ‖x‖ ≤ ‖y‖) (hYC : 1000 ≤ ‖y‖*‖c‖) (i : Fin 3) :
    (101/100 : ℝ)*(‖finiteN3Left x y c i‖+‖finiteN3Right x y c i‖) <
      4143*‖y‖^7*‖c‖^3 := by
  have hnorm := mul_le_mul_of_nonneg_left (finiteN3_root_columns_norm_le x y c hxy i)
    (show (0 : ℝ) ≤ 101/100 by norm_num)
  have hs := mul_lt_mul_of_pos_left (finiteN3_height_scalar (‖y‖*‖c‖) hYC)
    (pow_pos (norm_pos_iff.mpr hy) 4)
  have heq : (101/100 : ℝ)*(342*‖y‖^4+2352*‖y‖^5*‖c‖+
        5792*‖y‖^6*‖c‖^2+4096*‖y‖^7*‖c‖^3) <
      4143*‖y‖^7*‖c‖^3 := by nlinarith only [hs]
  exact hnorm.trans_lt heq

end D1Bound5
end
