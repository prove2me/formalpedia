-- Prove2me | solution 1 for BitDFT.buffer_shift_on_correct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T17:16:18.034451+00:00
-- url     : https://prove2.me/submissions/41134847-cb63-4efb-a38b-f0cf5a001677

import Definitions.Def_BitDFT_BufferShiftOn
import Theorems.Thm_BitDFT_alphabet_embedding_correct
import Theorems.Thm_BitDFT_buffer_shift_correct

noncomputable section
namespace BitDFT.BufferShiftOn
open IntMul

private theorem cfg_ext {M : MultitapeTM} (c d : M.Cfg)
    (hs : c.state = d.state) (hc : c.cells = d.cells) (hh : c.head = d.head) : c = d := by
  cases c; cases d; cases hs; cases hc; cases hh; rfl

theorem step_embed (N : MultitapeTM) (base : (machine N).Cfg) (c : (small N).Cfg) :
    (machine N).step (embed N base c) = embed N base ((small N).step c) := by
  have hj (j : Fin 2) : j.val ≤ 1 := by omega
  have hread : (fun j => (embed N base c).cells (oldTape N j)
      ((embed N base c).head (oldTape N j))) = (fun j => c.cells j (c.head j)) := by
    funext j
    simp [embed,oldTape,hj]
  apply cfg_ext
  · change ((small N).δ c.state _).1 = ((small N).δ c.state _).1
    rw [hread]
  · funext i
    by_cases hi : i.val ≤ 1
    · simp [MultitapeTM.step,control,transition,embed,oldTape,hi,hj]
    · simp [MultitapeTM.step,control,transition,embed,oldTape,hi,hj]
  · funext i
    by_cases hi : i.val ≤ 1
    · simp [MultitapeTM.step,control,transition,embed,oldTape,hi,hj]
    · simp [MultitapeTM.step,control,transition,embed,oldTape,hi,hj]

theorem run_embed (N : MultitapeTM) (base : (machine N).Cfg) (c : (small N).Cfg) (t : ℕ) :
    (machine N).step^[t] (embed N base c) = embed N base ((small N).step^[t] c) := by
  induction t with
  | zero => rfl
  | succ t ih => rw [Function.iterate_succ_apply',ih,step_embed,Function.iterate_succ_apply']

theorem shift_run (N : MultitapeTM) (base : (machine N).Cfg) (smallBase : BufferShift.machine.Cfg)
    (w : List Bool) :
    (machine N).step^[3*w.length+5]
      (embed N base (AlphabetEmbedding.embed (alphabetMap N)
        (BufferShift.frame smallBase .start (w.map BufferShift.machine.bitSym) (w.length+1)))) =
      embed N base (AlphabetEmbedding.embed (alphabetMap N)
        (BufferShift.frame smallBase .halt ([.blank]++w.map BufferShift.machine.bitSym++[.sep]) 1)) := by
  rw [run_embed]
  rw [(BitDFT.alphabet_embedding_correct BufferShift.machine N (alphabetMap N)).1]
  rw [BitDFT.buffer_shift_correct]

end BitDFT.BufferShiftOn

open BitDFT.BufferShiftOn BitDFT IntMul

theorem solution (N : MultitapeTM) (base : (machine N).Cfg) (smallBase : BufferShift.machine.Cfg)
    (w : List Bool) :
    let start := embed N base (AlphabetEmbedding.embed (alphabetMap N)
      (BufferShift.frame smallBase .start (w.map BufferShift.machine.bitSym) (w.length+1)))
    let finish := embed N base (AlphabetEmbedding.embed (alphabetMap N)
      (BufferShift.frame smallBase .halt ([.blank]++w.map BufferShift.machine.bitSym++[.sep]) 1))
    (machine N).step^[3*w.length+5] start = finish ∧
      (∀ i : Fin N.k, 2 ≤ i.val → finish.cells i = base.cells i ∧ finish.head i = base.head i) := by
  dsimp only
  refine ⟨shift_run N base smallBase w,?_⟩
  intro i hi
  have hn : ¬ i.val < 2 := by omega
  simp [embed,show ¬ i.val ≤ 1 by omega]
