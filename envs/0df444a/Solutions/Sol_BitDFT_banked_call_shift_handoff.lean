-- Prove2me | solution 1 for BitDFT.banked_call_shift_handoff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-25T04:04:35.682734+00:00
-- url     : https://prove2.me/submissions/d0ade992-3598-4ac0-8280-67d475a45d6f

import Definitions.Def_IntMul_TrackedBankedCall
import Definitions.Def_IntMul_TrackedOutputShift
import Theorems.Thm_BitDFT_banked_call_output_frame

set_option autoImplicit false
open IntMul

private theorem cfg_ext {M : MultitapeTM} (c d : M.Cfg)
    (hs : c.state = d.state) (hc : c.cells = d.cells) (hh : c.head = d.head) : c = d := by
  cases c
  cases d
  cases hs
  cases hc
  cases hh
  rfl

private theorem buffer_idempotent (M : MultitapeTM)
    (base : ℕ → TrackedBankedSimulation.Sym M) (w : List Bool) :
    TrackedOutputReturn.bufferTape M
      (TrackedOutputReturn.bufferTape M base 1 w) 1 w =
    TrackedOutputReturn.bufferTape M base 1 w := by
  funext p
  by_cases hp : p < 1
  · simp [TrackedOutputReturn.bufferTape, hp]
  · simp [TrackedOutputReturn.bufferTape, hp]

private def shiftView (M : MultitapeTM) (c : (TrackedBankedCall.machine M).Cfg) :
    (TrackedOutputShift.machine M).Cfg := ⟨.rewind, c.cells, c.head⟩

/-- A completed banked multiplier call is already in the exact rewind frame
    expected by the output-normalization controller. -/
theorem solution (M : MultitapeTM)
    (base : (TrackedBankedCall.machine M).Cfg)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (w : List Bool) :
    TrackedOutputShift.rewindFrame M
      (⟨.rewind,
        (TrackedBankedCall.finalFrame M base 1 offset extent c w).cells,
        (TrackedBankedCall.finalFrame M base 1 offset extent c w).head⟩ :
        (TrackedOutputShift.machine M).Cfg)
      w (w.length + 2) =
    (⟨.rewind,
      (TrackedBankedCall.finalFrame M base 1 offset extent c w).cells,
      (TrackedBankedCall.finalFrame M base 1 offset extent c w).head⟩ :
      (TrackedOutputShift.machine M).Cfg) := by
  change TrackedOutputShift.rewindFrame M (shiftView M (TrackedBankedCall.finalFrame M base 1 offset extent c w)) w (w.length + 2) = shiftView M (TrackedBankedCall.finalFrame M base 1 offset extent c w)
  apply cfg_ext
  · rfl
  · funext i
    by_cases hi : i.val = 1
    · have he : i = (TrackedOutputShift.machine M).outTape := Fin.ext hi
      rw [he]
      have hbuf : (TrackedBankedCall.finalFrame M base 1 offset extent c w).cells
          (TrackedBankedCall.machine M).outTape =
          TrackedOutputReturn.bufferTape M
            ((TrackedBankedCall.callBase M base).cells
              (TrackedBankedCall.machine M).outTape) 1 w := by
        simp [TrackedBankedCall.finalFrame, TrackedBankedCall.liftCall,
          TrackedReturnCall.finalFrame, TrackedReturnCall.liftCleanup,
          TrackedReturnCall.cleanupBase, TrackedReturnCall.returnBase,
          TrackedOutputReturn.finalFrame, TrackedOutputReturn.copyFrame,
          TrackedBankCleanup.finalFrame, MultitapeTM.outTape]
      change TrackedOutputReturn.bufferTape M
          ((TrackedBankedCall.finalFrame M base 1 offset extent c w).cells
            (TrackedBankedCall.machine M).outTape) 1 w =
        (TrackedBankedCall.finalFrame M base 1 offset extent c w).cells
          (TrackedBankedCall.machine M).outTape
      rw [hbuf]
      exact buffer_idempotent M _ w
    · simp [TrackedOutputShift.rewindFrame, shiftView, hi]
  · funext i
    by_cases hi : i.val = 1
    · have he : i = (TrackedOutputShift.machine M).outTape := Fin.ext hi
      rw [he]
      have hh := (BitDFT.banked_call_output_frame M base 1 offset extent c w 0).2
      change (TrackedBankedCall.finalFrame M base 1 offset extent c w).head
        (TrackedBankedCall.machine M).outTape = 1 + w.length + 1 at hh
      have hhead : (TrackedBankedCall.finalFrame M base 1 offset extent c w).head
          (TrackedBankedCall.machine M).outTape = w.length + 2 := by omega
      change w.length + 2 =
        (TrackedBankedCall.finalFrame M base 1 offset extent c w).head
          (TrackedBankedCall.machine M).outTape
      rw [hhead]
    · simp [TrackedOutputShift.rewindFrame, shiftView, hi]

