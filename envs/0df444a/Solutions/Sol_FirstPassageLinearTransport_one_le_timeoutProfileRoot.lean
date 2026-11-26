-- Prove2me | solution 1 for FirstPassageLinearTransport.one_le_timeoutProfileRoot
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:27:46.825772+00:00
-- url     : https://prove2.me/submissions/f497700a-7f74-4977-bdac-fd70e3196043

import Definitions.Def_FirstPassageLinearTransport_TimeoutRawClock
import Definitions.Def_FirstPassageLinearTransport_TimeoutTrajectoryProfile

set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution {M : ℕ} (hM : 1 ≤ M) :
    1 ≤ Real.sqrt (((M : ℝ) + 2) * Real.log ((M : ℝ) + 2)) := by
  have hx : (3 : ℝ) ≤ (M : ℝ) + 2 := by exact_mod_cast (by omega : 3 ≤ M + 2)
  have hlog : 1 ≤ Real.log ((M : ℝ) + 2) := by
    apply (Real.le_log_iff_exp_le (by positivity)).2
    exact Real.exp_one_lt_d9.le.trans (by linarith)
  rw [← Real.sqrt_one]
  apply Real.sqrt_le_sqrt
  nlinarith
end FirstPassageLinearTransport
