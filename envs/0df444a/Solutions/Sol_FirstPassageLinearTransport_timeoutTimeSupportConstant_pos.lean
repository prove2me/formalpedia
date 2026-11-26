-- Prove2me | solution 1 for FirstPassageLinearTransport.timeoutTimeSupportConstant_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:18:02.520452+00:00
-- url     : https://prove2.me/submissions/ba6d68e7-0b68-43ae-a1ba-6608a8a5ed9c

import Definitions.Def_FirstPassageLinearTransport_TimeoutRun
import Definitions.Def_FirstPassageLinearTransport_ShrinkingSchedules
import Definitions.Def_FirstPassageLinearTransport_TimeoutTimeSupport
import Theorems.Thm_FirstPassageLinearTransport_PowerDense_D_pos
import Theorems.Thm_FirstPassageLinearTransport_driftGap_pos


set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    (P : TimeoutHighRunData) (C : ℝ) :
    0 < timeoutTimeSupportConstant P C := by
  have hrHi0 : 0 < (P.rHi : ℝ) := P.pHi.r_pos
  have hsqrt1 : Real.sqrt (P.rHi : ℝ) < 1 := by
    nlinarith [Real.sq_sqrt hrHi0.le, Real.sqrt_nonneg (P.rHi : ℝ),
      P.pHi.r_lt_one]
  have hden : 0 < 1 - Real.sqrt (P.rHi : ℝ) := sub_pos.mpr hsqrt1
  have hnum : 0 ≤ P.D + P.tau + 3 := by
    linarith [P.D_pos, P.pHi.eta_pos]
  have hinner : 0 ≤
      (P.D + P.tau + 3) / (1 - Real.sqrt (P.rHi : ℝ)) +
        (C + 5) ^ 2 := by positivity
  have hratio : 0 ≤ 2 / driftGap :=
    div_nonneg (by norm_num) driftGap_pos.le
  unfold timeoutTimeSupportConstant
  nlinarith [mul_nonneg hratio hinner]
end FirstPassageLinearTransport
