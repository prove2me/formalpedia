-- Prove2me | solution 1 for FirstPassageLinearTransport.clockLeadingLt6953
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:28:34.21041+00:00
-- url     : https://prove2.me/submissions/56203c4e-6dc3-42fc-b39a-2a3bb7bcbd72

import Definitions.Def_FirstPassageLinearTransport_StretchedLogLanding
import Definitions.Def_FirstPassageLinearTransport_ClockBudget
import Theorems.Thm_FirstPassageLinearTransport_clockThreshold_lt_one


set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real Topology BigOperators
open Filter
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution {r : ℝ}
    (hr : r < clockThreshold) :
    1 / ((1 - r) * Real.log 2) < (6953 / 1000 : ℝ) := by
  have hclock : (0 : ℝ) < 6953 / 1000 := by norm_num
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hr1 : r < 1 := hr.trans clockThreshold_lt_one
  have hden : 0 < (1 - r) * Real.log 2 :=
    mul_pos (sub_pos.mpr hr1) hlog2
  rw [div_lt_iff₀ hden]
  unfold clockThreshold at hr
  have hclocklog : 0 < (6953 / 1000 : ℝ) * Real.log 2 :=
    mul_pos hclock hlog2
  have hbase : 1 / ((6953 / 1000 : ℝ) * Real.log 2) < 1 - r := by
    linarith
  rw [div_lt_iff₀ hclocklog] at hbase
  nlinarith
end FirstPassageLinearTransport
