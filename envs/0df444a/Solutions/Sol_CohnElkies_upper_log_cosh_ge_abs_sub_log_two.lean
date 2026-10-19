-- Prove2me | solution 1 for CohnElkies.upper_log_cosh_ge_abs_sub_log_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:28.839589+00:00
-- url     : https://prove2.me/submissions/69aa2e42-6f00-47b9-b9ce-5969403b480f

import Mathlib
import Definitions.Def_SpherePacking

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology BigOperators
namespace CohnElkies
theorem _root_.solution (x : ℝ) :
    |x| - Real.log 2 ≤ Real.log (Real.cosh x) := by
  have hhalf : Real.exp |x| / 2 ≤ Real.cosh x := by
    rw [← Real.cosh_abs, Real.cosh_eq]
    have hp := (Real.exp_pos (-|x|)).le
    linarith
  apply Real.exp_le_exp.mp
  rw [Real.exp_log (Real.cosh_pos x), Real.exp_sub,
    Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  exact hhalf
end CohnElkies
