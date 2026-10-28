-- Prove2me | solution 1 for BitDFT.work_counted_block_correct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T17:58:37.463599+00:00
-- url     : https://prove2.me/submissions/18737457-cc2f-48c6-a0b6-00da6fe811d9

import Theorems.Thm_BitDFT_work_relocation_correct
import Theorems.Thm_BitDFT_counted_block_correct

open IntMul

/-- Read the next counted block from a work tape, keeping the native input parked.
    Counter and template initialization are explicit prerequisites in the frame. -/
theorem solution (rootCells : ℕ → TapeCopy.Sym) (rootHead : ℕ)
    (pre out x y : List Bool) (hx : val y+1 ≤ x.length) :
    ∃ t : ℕ, t ≤ 6*(val y+1)+4*y.length+2 ∧
      (BitDFT.WorkRelocation.machine CountedStream.machine).step^[t]
        (BitDFT.WorkRelocation.embed CountedStream.machine rootCells rootHead
          (BitDFT.CountedBlock.frame pre out x y y.reverse 0 .emit)) =
      BitDFT.WorkRelocation.embed CountedStream.machine rootCells rootHead
          (BitDFT.CountedBlock.frame pre out x y y.reverse (val y+1) .halt) := by
  obtain ⟨t,ht,hr⟩ := BitDFT.counted_block_correct pre out x y hx
  refine ⟨t,ht,?_⟩
  rw [(BitDFT.work_relocation_correct CountedStream.machine rootCells rootHead
    (BitDFT.CountedBlock.frame pre out x y y.reverse 0 .emit) t).1,hr]
