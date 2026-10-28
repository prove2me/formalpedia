-- Prove2me | solution 1 for BitDFT.counted_block_correct_on_work_tapes
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-25T04:41:59.699697+00:00
-- url     : https://prove2.me/submissions/450e0a17-5f9c-4f1d-8ef2-0d181408fbf8

import Definitions.Def_BitDFT_CountedBlockOnWorkTapes
import Theorems.Thm_BitDFT_counted_block_correct

set_option autoImplicit false
open IntMul

theorem solution
    (base : BitDFT.CountedBlockOnWorkTapes.machine.Cfg)
    (pre out x y : List Bool) (hx : val y + 1 ≤ x.length) :
    ∃ t : ℕ, t ≤ 6*(val y+1)+4*y.length+2 ∧
      BitDFT.CountedBlockOnWorkTapes.machine.step^[t]
        (BitDFT.CountedBlockOnWorkTapes.embed base
          (BitDFT.CountedBlock.frame pre out x y y.reverse 0 .emit)) =
      BitDFT.CountedBlockOnWorkTapes.embed base
        (BitDFT.CountedBlock.frame pre out x y y.reverse (val y+1) .halt) := by
  obtain ⟨t, ht, hr⟩ := BitDFT.counted_block_correct pre out x y hx
  refine ⟨t, ht, ?_⟩
  rw [BitDFT.CountedBlockOnWorkTapes.run]
  exact congrArg (BitDFT.CountedBlockOnWorkTapes.embed base) hr
