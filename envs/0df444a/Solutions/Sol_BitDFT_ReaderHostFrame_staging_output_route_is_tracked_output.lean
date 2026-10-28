-- Prove2me | solution 1 for BitDFT.ReaderHostFrame.staging_output_route_is_tracked_output
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-25T18:37:52.833882+00:00
-- url     : https://prove2.me/submissions/348ab7ca-dfe7-46f3-b4ac-7f0da2bf88d3

import Definitions.Def_BitDFT_ReaderHostFrame_WorkSupport_v2
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section
open IntMul BitDFT.DedicatedTapeBanks BitDFT.BankedTripleAlphabetHost

theorem solution (A M H : MultitapeTM) :
    BitDFT.BankedOperandStage.multiplierOutputTape A M H =
      BitDFT.ReaderHostFrame.multiplierTapeRoute A M H
        (BitDFT.ReaderHostFrame.tracked M).outTape := by
  apply Fin.ext
  have hwork := BitDFT.DedicatedTapeBanks.multiplier_work_address A
    (BitDFT.ReaderHostFrame.tracked M) H
    (BitDFT.ReaderHostFrame.tracked M).outTape (by
      change 1 ≤ (BitDFT.ReaderHostFrame.tracked M).outTape.val
      rfl)
  have hval := congrArg Fin.val hwork
  have hout : (BitDFT.ReaderHostFrame.tracked M).outTape.val = 1 := rfl
  have hrouteVal : (BitDFT.ReaderHostFrame.multiplierTapeRoute A M H
      (BitDFT.ReaderHostFrame.tracked M).outTape).val = A.k := by
    simpa [BitDFT.ReaderHostFrame.multiplierTapeRoute,
      BitDFT.ReaderHostFrame.tracked, BitDFT.BankedTripleAlphabetHost.route,
      BitDFT.TapeExtension.oldTape, Fin.cast,
      BitDFT.DedicatedTapeBanks.multiplierOffset, hout]
      using hval
  change A.k = (BitDFT.ReaderHostFrame.multiplierTapeRoute A M H
    (BitDFT.ReaderHostFrame.tracked M).outTape).val
  exact hrouteVal.symm
end
