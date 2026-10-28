-- Prove2me | solution 1 for BitDFT.tape_count_transport_correct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T18:31:54.426072+00:00
-- url     : https://prove2.me/submissions/7d126f4a-3e05-4989-b014-1e878db72e96

import Definitions.Def_BitDFT_TapeCountTransport
open BitDFT.TapeCountTransport IntMul

/-- An arithmetic equality of tape counts introduces no machine transitions. -/
theorem solution (M : MultitapeTM) (n : ℕ) (h : M.k = n) (c : M.Cfg) (t : ℕ) :
    (machine M n h).step^[t] (embed M n h c) = embed M n h (M.step^[t] c) := by
  subst n
  rfl
