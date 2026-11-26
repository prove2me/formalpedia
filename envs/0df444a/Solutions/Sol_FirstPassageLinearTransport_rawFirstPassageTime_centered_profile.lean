-- Prove2me | solution 1 for FirstPassageLinearTransport.rawFirstPassageTime_centered_profile
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:27:30.599054+00:00
-- url     : https://prove2.me/submissions/990bc3ef-0cec-48e7-a373-eb22a529cb5c

import Definitions.Def_FirstPassageLinearTransport_TimeoutRawClock
import Definitions.Def_FirstPassageLinearTransport_TimeoutTrajectoryProfile
import Theorems.Thm_FirstPassageLinearTransport_rawFirstPassageTime_drift_profile
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
    (htube : ∀ i : ℕ, i ≤ rawTime n k → |rawLogDeviation n i| ≤ E) :
    |(rawFirstPassageTime n z : ℝ) -
        (3 / 2) * fixedPolylogClockCritical * Real.log ((n : ℝ) / z)| ≤
      (3 / 2) * fixedPolylogClockCritical * (E + Real.log 2) := by
  have hprofile := rawFirstPassageTime_drift_profile
    hn hzStart hk htube
  have hgapLog : 0 < driftGap * Real.log 2 :=
    mul_pos driftGap_pos (Real.log_pos (by norm_num))
  have hscale :
      (rawFirstPassageTime n z : ℝ) -
          (3 / 2) * fixedPolylogClockCritical * Real.log ((n : ℝ) / z) =
        (3 / 2) * fixedPolylogClockCritical *
          ((2 * driftGap / 3) * (rawFirstPassageTime n z : ℝ) *
            Real.log 2 - Real.log ((n : ℝ) / z)) := by
    unfold fixedPolylogClockCritical
    field_simp [hgapLog.ne', driftGap_pos.ne']
  rw [hscale, abs_mul,
    abs_of_pos (mul_pos (by norm_num) fixedPolylogClockCritical_pos)]
  exact mul_le_mul_of_nonneg_left hprofile
    (mul_nonneg (by norm_num) fixedPolylogClockCritical_pos.le)
end FirstPassageLinearTransport
