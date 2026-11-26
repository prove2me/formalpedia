-- Prove2me | solution 1 for FirstPassageLinearTransport.shortcutFirstPassageTime_centered_profile
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:24:25.578379+00:00
-- url     : https://prove2.me/submissions/0d50e8d3-a622-409d-9256-5aa2c9985b2f

import Definitions.Def_FirstPassageLinearTransport_TimeoutRawClock
import Definitions.Def_FirstPassageLinearTransport_TimeoutTrajectoryProfile
import Theorems.Thm_FirstPassageLinearTransport_shortcutFirstPassageTime_drift_profile
import Theorems.Thm_FirstPassageLinearTransport_driftGap_pos
import Theorems.Thm_FirstPassageLinearTransport_fixedPolylogClockCritical_pos


set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {n k : ℕ} {z E : ℝ}
    (hn : 0 < n) (hzStart : z < (n : ℝ))
    (hk : (orbit k n : ℝ) ≤ z)
    (htube : ∀ j : ℕ, j ≤ k → |shortcutLogDeviation n j| ≤ E) :
    |(shortcutFirstPassageTime n z : ℝ) -
        fixedPolylogClockCritical * Real.log ((n : ℝ) / z)| ≤
      fixedPolylogClockCritical * (E + Real.log 2) := by
  have hprofile := shortcutFirstPassageTime_drift_profile
    hn hzStart hk htube
  have hgapLog : 0 < driftGap * Real.log 2 :=
    mul_pos driftGap_pos (Real.log_pos (by norm_num))
  have hscale :
      (shortcutFirstPassageTime n z : ℝ) -
          fixedPolylogClockCritical * Real.log ((n : ℝ) / z) =
        fixedPolylogClockCritical *
          (driftGap * (shortcutFirstPassageTime n z : ℝ) * Real.log 2 -
            Real.log ((n : ℝ) / z)) := by
    unfold fixedPolylogClockCritical
    field_simp [hgapLog.ne', driftGap_pos.ne']
  rw [hscale, abs_mul,
    abs_of_pos fixedPolylogClockCritical_pos]
  exact mul_le_mul_of_nonneg_left hprofile fixedPolylogClockCritical_pos.le
end FirstPassageLinearTransport
