-- Prove2me | solution 1 for FirstPassageLinearTransport.timeoutTimePotential_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:18:09.621863+00:00
-- url     : https://prove2.me/submissions/6f717ad5-4bd4-493f-95fe-0cc6529ec10a

import Definitions.Def_FirstPassageLinearTransport_TimeoutRun
import Definitions.Def_FirstPassageLinearTransport_ShrinkingSchedules
import Definitions.Def_FirstPassageLinearTransport_TimeoutTimeSupport
import Theorems.Thm_FirstPassageLinearTransport_PowerDense_D_pos

section
namespace FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section
private theorem timeout_sqrt_rat_lt_one
    {r : ℚ} (hr1 : r < 1) :
    Real.sqrt (r : ℝ) < 1 := by
  rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < 1)]
  norm_num
  exact_mod_cast hr1
end
end FirstPassageLinearTransport
end

set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    (P : TimeoutHighRunData) (M S q : ℕ) :
    0 ≤ timeoutTimePotential P M S q := by
  have hdHi : 0 < 1 - Real.sqrt (P.rHi : ℝ) := sub_pos.mpr
    (timeout_sqrt_rat_lt_one
      (by exact_mod_cast P.pHi.r_lt_one : P.rHi < 1))
  have hcoefHi : 0 ≤ P.D + P.tau + 3 := by
    nlinarith [P.D_pos, P.pHi.eta_pos]
  unfold timeoutTimePotential
  split_ifs <;> positivity
end FirstPassageLinearTransport
