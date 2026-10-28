-- Prove2me | solution 1 for BitDFT.record_terminator_step
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T19:34:20.316536+00:00
-- url     : https://prove2.me/submissions/e368329f-0360-43dd-b09c-e6f03e231f0b

import Definitions.Def_BitDFT_RecordTerminator
open BitDFT.RecordTerminator IntMul

theorem solution (M : MultitapeTM) (cells : Fin (storage M).k → ℕ → (storage M).Sym)
    (head : Fin (storage M).k → ℕ)
    (hblank : cells (target M) (head (target M)) = (storage M).blank) :
    (controlMachine M).step ⟨false,cells,head⟩ =
      ⟨true, Function.update cells (target M)
        (Function.update (cells (target M)) (head (target M)) (storage M).sep), head⟩ := by
  exact control_step M cells head hblank
