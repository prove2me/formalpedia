-- Prove2me | solution 1 for BitDFT.banked_call_output_shift
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-25T04:06:55.451918+00:00
-- url     : https://prove2.me/submissions/4ab4a16a-8a7f-4945-8702-e7d744cf400d

import Definitions.Def_IntMul_TrackedBankedCall
import Definitions.Def_IntMul_TrackedOutputShift
import Theorems.Thm_IntMul_TrackedOutputShift_shift_correct
import Theorems.Thm_BitDFT_banked_call_shift_handoff

set_option autoImplicit false
open IntMul

theorem solution (M : MultitapeTM)
    (base : (TrackedBankedCall.machine M).Cfg)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (w : List Bool) :
    (TrackedOutputShift.machine M).step^[4 * w.length + 4]
      (⟨.rewind,
        (TrackedBankedCall.finalFrame M base 1 offset extent c w).cells,
        (TrackedBankedCall.finalFrame M base 1 offset extent c w).head⟩ :
        (TrackedOutputShift.machine M).Cfg) =
    TrackedOutputShift.finalFrame M
      (⟨.rewind,
        (TrackedBankedCall.finalFrame M base 1 offset extent c w).cells,
        (TrackedBankedCall.finalFrame M base 1 offset extent c w).head⟩ :
        (TrackedOutputShift.machine M).Cfg) w := by
  let start : (TrackedOutputShift.machine M).Cfg := ⟨.rewind,
    (TrackedBankedCall.finalFrame M base 1 offset extent c w).cells,
    (TrackedBankedCall.finalFrame M base 1 offset extent c w).head⟩
  have hr := TrackedOutputShift.shift_correct M start w
  rw [BitDFT.banked_call_shift_handoff M base offset extent c w] at hr
  exact hr
