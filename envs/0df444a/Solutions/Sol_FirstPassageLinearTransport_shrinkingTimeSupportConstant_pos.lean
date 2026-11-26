-- Prove2me | solution 1 for FirstPassageLinearTransport.shrinkingTimeSupportConstant_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:49:05.519749+00:00
-- url     : https://prove2.me/submissions/e022b2d8-ef98-4e96-8d20-0dd21c20740f

import Definitions.Def_FirstPassageLinearTransport_ShrinkingTimeSupport
import Definitions.Def_FirstPassageLinearTransport_PolylogTerminalSchedule
import Definitions.Def_FirstPassageLinearTransport_TwoRegimeClock
import Definitions.Def_FirstPassageLinearTransport_ShrinkingSchedules
import Theorems.Thm_FirstPassageLinearTransport_PowerDense_D_pos
import Theorems.Thm_FirstPassageLinearTransport_driftGap_pos


set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    (P : ShrinkingBarrierRunData) {C : ℝ} (hC : 0 ≤ C) :
    0 < shrinkingTimeSupportConstant P C := by
  have hsqrt : Real.sqrt (P.rHi : ℝ) < 1 := by
    rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < 1)]
    norm_num
    exact_mod_cast P.pHi.r_lt_one
  have hrLo : (P.rLo : ℝ) < 1 := by exact_mod_cast P.pLo.r_lt_one
  unfold shrinkingTimeSupportConstant
  have hD : 0 < P.D + P.tau + 3 := by
    nlinarith [P.D_pos, P.pHi.eta_pos]
  have hLo : 0 < 2 * P.etaLo + 3 := by nlinarith [P.pLo.eta_pos]
  have hinner : 0 <
      (P.D + P.tau + 3) / (1 - Real.sqrt (P.rHi : ℝ)) +
        (2 * P.etaLo + 3) * (C + 1) / (1 - (P.rLo : ℝ)) := by
    apply add_pos
    · exact div_pos hD (sub_pos.mpr hsqrt)
    · exact div_pos (mul_pos hLo (by linarith)) (sub_pos.mpr hrLo)
  have hscale : 0 < 2 / driftGap := div_pos (by norm_num) driftGap_pos
  nlinarith [mul_pos hscale hinner]
end FirstPassageLinearTransport
