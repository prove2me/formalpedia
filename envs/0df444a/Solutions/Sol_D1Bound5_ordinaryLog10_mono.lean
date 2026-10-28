-- Prove2me | solution 1 for D1Bound5.ordinaryLog10_mono
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:31:05.274212+00:00
-- url     : https://prove2.me/submissions/614df856-285a-4300-9a0e-3f1be7b0f274

import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Definitions.Def_D1Bound5_OrdinaryLog10_Definitions
import Theorems.Thm_D1Bound5_ordinaryLog10_base_pos

section
namespace D1Bound5













theorem _root_.solution {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    ordinaryLog10 x ≤ ordinaryLog10 y := by
  exact div_le_div_of_nonneg_right (Real.log_le_log hx hxy) ordinaryLog10_base_pos.le









end D1Bound5
end
