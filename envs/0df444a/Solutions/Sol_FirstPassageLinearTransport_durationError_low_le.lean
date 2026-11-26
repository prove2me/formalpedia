-- Prove2me | solution 1 for FirstPassageLinearTransport.durationError_low_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:45:42.467721+00:00
-- url     : https://prove2.me/submissions/d03d3700-ce61-4a7f-8a31-ad09e73988c5

import Definitions.Def_FirstPassageLinearTransport_ShrinkingBarrierRun
import Definitions.Def_FirstPassageLinearTransport_ShrinkingTimeSupport

set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    (P : ShrinkingBarrierRunData) {m : ℕ} (hm : 1 ≤ m) :
    durationError P.etaLo m ≤ (2 * P.etaLo + 3) * (m : ℝ) := by
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  unfold durationError
  nlinarith [P.pLo.eta_pos.le]
end FirstPassageLinearTransport
