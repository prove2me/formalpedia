-- Prove2me | solution 1 for BitDFT.work_signed_block_correct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T18:49:49.399534+00:00
-- url     : https://prove2.me/submissions/d350e2e4-3aa9-427d-a078-9a07ff95d1a1

import Theorems.Thm_BitDFT_work_relocation_correct
import Theorems.Thm_BitDFT_signed_block_correct

open IntMul BitDFT.SignedBlock

theorem solution (rootCells : ℕ → TapeCopy.Sym) (rootHead : ℕ)
    (pre out : List Bool) (sign : Bool) (x y : List Bool) (hx : val y+1 ≤ x.length) :
    ∃ t : ℕ, t ≤ 6*(val y+1)+4*y.length+4 ∧
      (BitDFT.WorkRelocation.machine machine).step^[t]
        (BitDFT.WorkRelocation.embed machine rootCells rootHead (initial pre out sign x y)) =
      BitDFT.WorkRelocation.embed machine rootCells rootHead (final pre out sign x y) := by
  obtain ⟨t,ht,hr⟩ := BitDFT.signed_block_correct pre out sign x y hx
  refine ⟨t,ht,?_⟩
  rw [(BitDFT.work_relocation_correct machine rootCells rootHead
    (initial pre out sign x y) t).1,hr]
