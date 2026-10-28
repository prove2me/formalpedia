-- Prove2me | solution 1 for BitDFT.suffix_then_serializer
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-25T07:14:32.590423+00:00
-- url     : https://prove2.me/submissions/d76b83f1-2c62-4089-825f-1eefc2f83612

import Definitions.Def_BitDFT_SerializerControllerBridge

set_option autoImplicit false
noncomputable section
open IntMul BitDFT.MachineSequence BitDFT.RoutedCountedBlockFreshTapes

theorem solution (M : MultitapeTM)
    (C : Controller (source M))
    (extraCells : Fin (extension M).k → ℕ → (source M).Sym)
    (extraHeads : Fin (extension M).k → ℕ)
    (c cEnd : C.machine.Cfg) (ts tr : ℕ)
    (hRun : C.machine.step^[ts] c = cEnd)
    (hNoEarlyExit : ∀ s, s < ts →
      ((suffixControllerOnSerializerHost M C).machine.step^[s]
        (suffixEmbed M C extraCells extraHeads c)).state ≠ C.exit)
    (hExit : cEnd.state = C.exit)
    (serStart serEnd : (serializerController M).machine.Cfg)
    (hFrame : BitDFT.MachineSequence.handoff (suffixControllerOnSerializerHost M C)
      (serializerController M) (suffixEmbed M C extraCells extraHeads cEnd) = serStart)
    (hSer : (serializerController M).machine.step^[tr] serStart = serEnd) :
    (suffixSerializerController M C).machine.step^[ts+1+tr]
      (BitDFT.MachineSequence.leftCfg (suffixControllerOnSerializerHost M C)
        (serializerController M) (suffixEmbed M C extraCells extraHeads c)) =
      BitDFT.MachineSequence.rightCfg (suffixControllerOnSerializerHost M C)
        (serializerController M) serEnd := by
  exact suffix_then_serializer M C extraCells extraHeads c cEnd ts tr
    hRun hNoEarlyExit hExit serStart serEnd hFrame hSer

end
