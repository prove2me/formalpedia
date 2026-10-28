-- Prove2me | solution 1 for BitDFT.signed_block_initial_match
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T18:56:18.502997+00:00
-- url     : https://prove2.me/submissions/4c442ec9-4c99-45e6-8a53-626d47d662ed

import Definitions.Def_BitDFT_SignedBlockPlacement
import Mathlib.Tactic
set_option maxHeartbeats 1000000
namespace BitDFT.SignedBlockSlots
open IntMul SignedBlockPlacement

private theorem slot (N : MultitapeTM) (k : ℕ)
    (cells : Fin (5+(k+3)) → ℕ → N.Sym) (heads : Fin (5+(k+3)) → ℕ)
    (c : storage.Cfg) (j : Fin 5) :
    let i : Fin (5+(k+3)) := ⟨j.val,by have := j.isLt; omega⟩
    (embed N k cells heads c).cells (routing k i) =
      (fun p => PreprocessorAlphabet.encode N (c.cells j p)) ∧
    (embed N k cells heads c).head (routing k i) = c.head j := by
  simp [embed,TapePermutation.embed,TapeExtension.embed,AlphabetEmbedding.embed,
    alphabetMap,PreprocessorAlphabet.alphabetMap,j.isLt]
  rfl

private theorem tape_embed (N : MultitapeTM) (w : List TapeCopy.Sym) :
    (fun p => PreprocessorAlphabet.encode N (CountedStream.machine.tapeOf w p)) =
      N.tapeOf (w.map (PreprocessorAlphabet.encode N)) := by
  funext p
  cases p with
  | zero => rfl
  | succ p =>
    simp only [MultitapeTM.tapeOf,List.getD_eq_getElem?_getD,List.getElem?_map]
    cases h : w[p]? <;> simp [h,PreprocessorAlphabet.encode]

private theorem bits (N : MultitapeTM) (y : List Bool) :
    (y.map CountedStream.machine.bitSym).map (PreprocessorAlphabet.encode N) = y.map N.bitSym := by
  rw [List.map_map]
  congr 1
  funext b
  cases b <;> rfl

end BitDFT.SignedBlockSlots
open BitDFT.SignedBlockSlots BitDFT.SignedBlockPlacement BitDFT IntMul

private theorem slot_layout (N : MultitapeTM) (k : ℕ)
    (cells : Fin (5+(k+3)) → ℕ → N.Sym) (heads : Fin (5+(k+3)) → ℕ)
    (rootCells : ℕ → TapeCopy.Sym) (rootHead : ℕ)
    (pre out : List Bool) (sign : Bool) (x y : List Bool) :
    let start := embed N k cells heads (WorkRelocation.embed SignedBlock.machine rootCells rootHead
      (SignedBlock.initial pre out sign x y))
    start.cells ⟨1,by change 1 < 5+(k+3); omega⟩ = N.tapeOf ((pre++sign::x).map N.bitSym) ∧
    start.head ⟨1,by change 1 < 5+(k+3); omega⟩ = pre.length+1 ∧
    start.cells (scratchTape k) = N.tapeOf (out.map N.bitSym) ∧
    start.head (scratchTape k) = out.length+1 ∧
    start.cells (counterTape k) = N.tapeOf (N.sep :: (y.map N.bitSym ++ [N.sep])) ∧
    start.head (counterTape k) = y.length+1 ∧
    start.cells (templateTape k) = N.tapeOf (N.sep :: (y.map N.bitSym ++ [N.sep])) ∧
    start.head (templateTape k) = y.length+1 := by
  let c := WorkRelocation.embed SignedBlock.machine rootCells rootHead (SignedBlock.initial pre out sign x y)
  have s1 := slot N k cells heads c ⟨1,by decide⟩
  have s2 := slot N k cells heads c ⟨2,by decide⟩
  have s3 := slot N k cells heads c ⟨3,by decide⟩
  have s4 := slot N k cells heads c ⟨4,by decide⟩
  dsimp only at s1 s2 s3 s4
  rw [routing_one] at s1
  rw [routing_two] at s2
  rw [routing_three] at s3
  rw [routing_four] at s4
  have hf : PreprocessorAlphabet.encode N ∘ CountedStream.machine.bitSym = N.bitSym := by
    funext b
    cases b <;> rfl
  have hsign : PreprocessorAlphabet.encode N (CountedStream.machine.bitSym sign) = N.bitSym sign := by
    cases sign <;> rfl
  simp [c,WorkRelocation.embed,WorkRelocation.innerTape,SignedBlock.initial,
    MachineSequence.leftCfg,SignedBlock.signStart,CountedBlock.frame,
    tape_embed,bits,hf,hsign,show PreprocessorAlphabet.encode N TapeCopy.Sym.sep = N.sep from rfl] at s1 s2 s3 s4 ⊢
  exact ⟨s1.1,s1.2,s2.1,s2.2,s3.1,s3.2,s4.1,s4.2⟩

private theorem cfg_ext {M : MultitapeTM} (c d : M.Cfg)
    (hs : c.state = d.state) (hc : c.cells = d.cells) (hh : c.head = d.head) : c = d := by
  cases c; cases d; cases hs; cases hc; cases hh; rfl

theorem reconstruct (N : MultitapeTM) (k : ℕ) (d : (machine N k).Cfg)
    (c : storage.Cfg) (hs : d.state = c.state)
    (hc : ∀ j : Fin 5,
      d.cells (routing k ⟨j.val,by have := j.isLt; omega⟩) =
        fun p => PreprocessorAlphabet.encode N (c.cells j p))
    (hh : ∀ j : Fin 5,
      d.head (routing k ⟨j.val,by have := j.isLt; omega⟩) = c.head j) :
    embed N k d.cells d.head c = d := by
  apply cfg_ext
  · exact hs.symm
  · funext i
    have he : i = routing k ((routing k).symm i) := (Equiv.apply_symm_apply _ _).symm
    by_cases hj : ((routing k).symm i).val < 5
    · let j : Fin 5 := ⟨((routing k).symm i).val,hj⟩
      have hi : i = routing k ⟨j.val,by have := j.isLt; omega⟩ := he
      rw [hi]
      exact (slot N k d.cells d.head c j).1.trans (hc j).symm
    · have hn : ¬((routing k).symm i).val < (lifted N).k := hj
      simp [embed,TapePermutation.embed,TapeExtension.embed,hn]
  · funext i
    have he : i = routing k ((routing k).symm i) := (Equiv.apply_symm_apply _ _).symm
    by_cases hj : ((routing k).symm i).val < 5
    · let j : Fin 5 := ⟨((routing k).symm i).val,hj⟩
      have hi : i = routing k ⟨j.val,by have := j.isLt; omega⟩ := he
      rw [hi]
      exact (slot N k d.cells d.head c j).2.trans (hh j).symm
    · have hn : ¬((routing k).symm i).val < (lifted N).k := hj
      simp [embed,TapePermutation.embed,TapeExtension.embed,hn]

theorem solution (N : MultitapeTM) (k : ℕ) (d : (machine N k).Cfg)
    (rootCells : ℕ → TapeCopy.Sym) (rootHead : ℕ)
    (pre out : List Bool) (sign : Bool) (x y : List Bool)
    (hs : d.state = (machine N k).qStart)
    (hroot : d.cells ⟨0,by change 0 < 5+(k+3); omega⟩ = fun p => PreprocessorAlphabet.encode N (rootCells p))
    (hrootHead : d.head ⟨0,by change 0 < 5+(k+3); omega⟩ = rootHead)
    (hv : d.cells ⟨1,by change 1 < 5+(k+3); omega⟩ = N.tapeOf ((pre++sign::x).map N.bitSym))
    (hvHead : d.head ⟨1,by change 1 < 5+(k+3); omega⟩ = pre.length+1)
    (ho : d.cells (scratchTape k) = N.tapeOf (out.map N.bitSym))
    (hoHead : d.head (scratchTape k) = out.length+1)
    (hc : d.cells (counterTape k) = N.tapeOf (N.sep :: (y.map N.bitSym ++ [N.sep])))
    (hcHead : d.head (counterTape k) = y.length+1)
    (ht : d.cells (templateTape k) = N.tapeOf (N.sep :: (y.map N.bitSym ++ [N.sep])))
    (htHead : d.head (templateTape k) = y.length+1) :
    embed N k d.cells d.head (WorkRelocation.embed SignedBlock.machine rootCells rootHead
      (SignedBlock.initial pre out sign x y)) = d := by
  have hl := slot_layout N k d.cells d.head rootCells rootHead pre out sign x y
  apply reconstruct N k d _ hs
  · intro j
    have hslot := (slot N k d.cells d.head
      (WorkRelocation.embed SignedBlock.machine rootCells rootHead (SignedBlock.initial pre out sign x y)) j).1
    fin_cases j
    · change d.cells (routing k (0 : Fin (5+(k+3)))) = _
      rw [show routing k (0 : Fin (5+(k+3))) = 0 from routing_zero k]
      exact hroot
    · apply Eq.trans _ hslot
      simpa only [routing_one] using hv.trans hl.1.symm
    · apply Eq.trans _ hslot
      simpa only [routing_two] using ho.trans hl.2.2.1.symm
    · apply Eq.trans _ hslot
      simpa only [routing_three] using hc.trans hl.2.2.2.2.1.symm
    · apply Eq.trans _ hslot
      simpa only [routing_four] using ht.trans hl.2.2.2.2.2.2.1.symm
  · intro j
    have hslot := (slot N k d.cells d.head
      (WorkRelocation.embed SignedBlock.machine rootCells rootHead (SignedBlock.initial pre out sign x y)) j).2
    fin_cases j
    · change d.head (routing k (0 : Fin (5+(k+3)))) = _
      rw [show routing k (0 : Fin (5+(k+3))) = 0 from routing_zero k]
      exact hrootHead
    · apply Eq.trans _ hslot
      simpa only [routing_one] using hvHead.trans hl.2.1.symm
    · apply Eq.trans _ hslot
      simpa only [routing_two] using hoHead.trans hl.2.2.2.1.symm
    · apply Eq.trans _ hslot
      simpa only [routing_three] using hcHead.trans hl.2.2.2.2.2.1.symm
    · apply Eq.trans _ hslot
      simpa only [routing_four] using htHead.trans hl.2.2.2.2.2.2.2.symm
