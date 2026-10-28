-- Prove2me | solution 1 for D1Bound5.finiteN2_height_scaled
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:19:06.796395+00:00
-- url     : https://prove2.me/submissions/a96cb737-1482-40c5-a348-43ae2a0fd573

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
import Definitions.Def_D1Bound5_FiniteN2Matrix_Definitions
import Theorems.Thm_D1Bound5_finiteN2_root_columns_norm_le

section
namespace D1Bound5













/-- Exact rational slack producing the manuscript's integer constant243. -/
theorem finiteN2_height_scalar (T : ℝ) (hT : 1000 ≤ T) :
    (101/100 : ℝ)*(50+200*T+240*T^2) < 243*T^2 := by
  have hp := mul_nonneg (sub_nonneg.mpr hT) (show 0 ≤ T by linarith only [hT])
  nlinarith only [hp,hT]

/-- Actual N2 root-column height, with the paper's sharp constant. -/
theorem _root_.solution (x y c : ℂ) (hy : y ≠ 0)
    (hxy : ‖x‖ ≤ ‖y‖) (hYC : 1000 ≤ ‖y‖*‖c‖) (i : Fin 3) :
    (101/100 : ℝ)*(‖finiteN2Left x y c i‖+‖finiteN2Right x y c i‖) <
      243*‖y‖^4*‖c‖^2 := by
  have hnorm := mul_le_mul_of_nonneg_left (finiteN2_root_columns_norm_le x y c hxy i)
    (show (0 : ℝ) ≤ 101/100 by norm_num)
  have hs := mul_lt_mul_of_pos_left (finiteN2_height_scalar (‖y‖*‖c‖) hYC)
    (sq_pos_of_pos (norm_pos_iff.mpr hy))
  have heq : (101/100 : ℝ)*(50*‖y‖^2+200*‖y‖^3*‖c‖+240*‖y‖^4*‖c‖^2) <
      243*‖y‖^4*‖c‖^2 := by nlinarith only [hs]
  exact hnorm.trans_lt heq

end D1Bound5
end
