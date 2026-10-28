-- Prove2me | solution 1 for BitDFT.banked_call_output_frame
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-25T03:57:46.695681+00:00
-- url     : https://prove2.me/submissions/1a062dbe-0a3d-4bd2-b069-3329f725d5e4

import Definitions.Def_IntMul_TrackedBankedCall

set_option autoImplicit false
open IntMul

private theorem output_head (M : MultitapeTM)
    (base : (TrackedBankedCall.machine M).Cfg)
    (sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg) (w : List Bool) :
    (TrackedBankedCall.finalFrame M base sigma offset extent c w).head
      (TrackedBankedCall.machine M).outTape = sigma + w.length + 1 := by
    simp [TrackedBankedCall.finalFrame, TrackedBankedCall.liftCall,
    TrackedReturnCall.finalFrame, TrackedReturnCall.liftCleanup,
    TrackedReturnCall.cleanupBase, TrackedReturnCall.returnBase,
    TrackedOutputReturn.finalFrame, TrackedOutputReturn.copyFrame,
    TrackedBankCleanup.finalFrame, MultitapeTM.outTape]

/-- The tracked multiplier's returned output is stored after the caller
    marker as tagged symbols, with a blank, unvisited tail. -/
theorem solution (M : MultitapeTM)
    (base : (TrackedBankedCall.machine M).Cfg)
    (sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg) (w : List Bool)
    (j : ℕ) :
    (TrackedBankedCall.finalFrame M base sigma offset extent c w).cells
      (TrackedBankedCall.machine M).outTape (sigma + j + 1) =
        some ((w.map M.bitSym).getD j M.blank, decide (j < w.length)) ∧
    (TrackedBankedCall.finalFrame M base sigma offset extent c w).head
      (TrackedBankedCall.machine M).outTape = sigma + w.length + 1 := by
  constructor
  ·
    have hlt : ¬ sigma + j + 1 < sigma := by omega
    have hne : sigma + j + 1 ≠ sigma := by omega
    have hidx : sigma + j + 1 - sigma - 1 = j := by omega
    simp [TrackedBankedCall.finalFrame, TrackedBankedCall.liftCall,
      TrackedReturnCall.finalFrame, TrackedReturnCall.liftCleanup,
      TrackedReturnCall.cleanupBase, TrackedReturnCall.returnBase,
      TrackedOutputReturn.finalFrame, TrackedOutputReturn.copyFrame,
      TrackedOutputReturn.bufferTape, TrackedBankCleanup.finalFrame,
      TrackedBankCleanup.freshTape, MultitapeTM.outTape, hlt, hne, hidx]
  · exact output_head M base sigma offset extent c w
