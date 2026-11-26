-- Prove2me | solution 1 for FirstPassageLinearTransport.stageRawClock_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:40:25.126921+00:00
-- url     : https://prove2.me/submissions/c13df9b3-c9fb-44c7-b33e-537cadf02ed0

import Definitions.Def_FirstPassageLinearTransport_RawDynamics
import Definitions.Def_FirstPassageLinearTransport_ClockBudget
import Definitions.Def_FirstPassageLinearTransport_RawClockBudget
import Theorems.Thm_FirstPassageLinearTransport_oddCount_stageClock_le
import Theorems.Thm_FirstPassageLinearTransport_clockGeom_nonneg
import Theorems.Thm_FirstPassageLinearTransport_stageClock_le_logb
import Theorems.Thm_FirstPassageLinearTransport_stageK_one_le


set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {r eta : ℝ} (p : StageSetup r eta) {R n : ℕ}
    (hn : 0 < n) (hnSet : n ∈ bootstrapSet p R) :
    (rawTime n (stageClock p R n) : ℝ) ≤
      clockGeom r R *
          (3 / (2 * Real.log 2) + eta / Real.log 3) * Real.log n +
        (R : ℝ) ^ 2 *
          (3 / 2 * Real.logb 2 (stageK p) +
            eta / Real.log 3 * Real.log (stageK p)) := by
  have hclock := stageClock_le_logb p hn hnSet
  have hodd := oddCount_stageClock_le p hn hnSet
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hgeom0 := clockGeom_nonneg p.r_pos.le R
  have hlogn0 : 0 ≤ Real.log n := by
    apply Real.log_nonneg
    exact_mod_cast (show 1 ≤ n by omega)
  have hlogK0 : 0 ≤ Real.log (stageK p) :=
    Real.log_nonneg (stageK_one_le p)
  have hlogbK0 : 0 ≤ Real.logb 2 (stageK p) :=
    Real.logb_nonneg (by norm_num) (stageK_one_le p)
  have hclockScaled := mul_le_mul_of_nonneg_left hclock (by norm_num :
    (0 : ℝ) ≤ 3 / 2)
  have hrawFirst :
      (rawTime n (stageClock p R n) : ℝ) ≤
        3 / 2 * (stageClock p R n : ℝ) +
          eta / Real.log 3 *
            (clockGeom r R * Real.log n +
              (R : ℝ) ^ 2 * Real.log (stageK p)) := by
    unfold rawTime
    push_cast
    linarith
  calc
    (rawTime n (stageClock p R n) : ℝ) ≤
        3 / 2 * (stageClock p R n : ℝ) +
          eta / Real.log 3 *
            (clockGeom r R * Real.log n +
              (R : ℝ) ^ 2 * Real.log (stageK p)) := hrawFirst
    _ ≤ 3 / 2 *
          (clockGeom r R * Real.logb 2 n +
            (R : ℝ) ^ 2 * Real.logb 2 (stageK p)) +
          eta / Real.log 3 *
            (clockGeom r R * Real.log n +
              (R : ℝ) ^ 2 * Real.log (stageK p)) := by
      gcongr
    _ = clockGeom r R *
          (3 / (2 * Real.log 2) + eta / Real.log 3) * Real.log n +
        (R : ℝ) ^ 2 *
          (3 / 2 * Real.logb 2 (stageK p) +
            eta / Real.log 3 * Real.log (stageK p)) := by
      rw [Real.logb]
      ring
end FirstPassageLinearTransport
