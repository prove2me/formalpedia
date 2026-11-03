-- Prove2me | solution 1 for BitDFT.unpackerMachine_stuck
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T05:31:48.091734+00:00
-- url     : https://prove2.me/submissions/b4be993d-a75d-40d8-b445-9f1d03c3347d

import Mathlib
import Definitions.Def_BitDFT_unpackerMachine

set_option autoImplicit false
noncomputable section

theorem solution (x y : List Bool) :
    (BitDFT.Unpacker.machine.step (BitDFT.Unpacker.machine.initCfg x y)).head
      BitDFT.Unpacker.machine.inTape = 0 := by
  delta BitDFT.Unpacker.machine
  simp only [IntMul.MultitapeTM.step, IntMul.MultitapeTM.initCfg, BitDFT.Unpacker.spec,
    BitDFT.Unpacker.guard]
  rfl
