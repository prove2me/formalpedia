-- Prove2me | solution 1 for BitDFT.tape_permutation_run
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T15:15:29.461174+00:00
-- url     : https://prove2.me/submissions/a4a7f8c5-e941-4b9e-a728-5743e472573a

import Definitions.Def_BitDFT_TapePermutation
namespace BitDFT.TapePermutation
open IntMul
private theorem cfg_ext {M : MultitapeTM} (c d : M.Cfg)
    (hs : c.state = d.state) (hc : c.cells = d.cells) (hh : c.head = d.head) : c = d := by
  cases c; cases d; cases hs; cases hc; cases hh; rfl

theorem step_embed (M : MultitapeTM) (e : Fin M.k ≃ Fin M.k) (he : e M.inTape = M.inTape)
    (c : M.Cfg) :
    (machine M e he).step (embed M e he c) = embed M e he (M.step c) := by
  apply cfg_ext
  · simp [MultitapeTM.step,transition,embed]
  · funext i; simp [MultitapeTM.step,transition,embed]
  · funext i; simp [MultitapeTM.step,transition,embed]

end BitDFT.TapePermutation

open BitDFT.TapePermutation IntMul

theorem solution (M : MultitapeTM) (e : Fin M.k ≃ Fin M.k) (he : e M.inTape = M.inTape)
    (c : M.Cfg) (t : ℕ) :
    (machine M e he).step^[t] (embed M e he c) = embed M e he (M.step^[t] c) := by
  induction t with
  | zero => rfl
  | succ t ih => rw [Function.iterate_succ_apply',ih,step_embed,Function.iterate_succ_apply']

