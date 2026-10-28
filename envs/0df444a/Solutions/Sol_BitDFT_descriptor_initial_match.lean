-- Prove2me | solution 1 for BitDFT.descriptor_initial_match
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T18:22:29.728837+00:00
-- url     : https://prove2.me/submissions/9e97d3de-070d-40b6-8037-624493a6cd90

import Definitions.Def_BitDFT_DescriptorPlacement
import Mathlib.Tactic
namespace BitDFT.DescriptorSlots
open IntMul DescriptorPlacement

private theorem slot (N : MultitapeTM) (k : ℕ)
    (cells : Fin (4+(k+3)) → ℕ → N.Sym) (heads : Fin (4+(k+3)) → ℕ)
    (c : RewoundDescriptor.machine.Cfg) (j : Fin 4) :
    let i : Fin (4+(k+3)) := ⟨j.val,by have := j.isLt; omega⟩
    (embed N k cells heads c).cells (routing k i) =
      (fun p => PreprocessorAlphabet.encode N (c.cells j p)) ∧
    (embed N k cells heads c).head (routing k i) = c.head j := by
  simp [embed,TapePermutation.embed,TapeExtension.embed,AlphabetEmbedding.embed,
    alphabetMap,PreprocessorAlphabet.alphabetMap,j.isLt]
  rfl

private theorem tape_embed (N : MultitapeTM) (w : List TapeCopy.Sym) :
    (fun p => PreprocessorAlphabet.encode N (DescriptorSetup.machine.tapeOf w p)) =
      N.tapeOf (w.map (PreprocessorAlphabet.encode N)) := by
  funext p
  cases p with
  | zero => rfl
  | succ p =>
    simp only [MultitapeTM.tapeOf,List.getD_eq_getElem?_getD,List.getElem?_map]
    cases h : w[p]? <;> simp [h,PreprocessorAlphabet.encode]

private theorem bits (N : MultitapeTM) (y : List Bool) :
    (y.map DescriptorSetup.machine.bitSym).map (PreprocessorAlphabet.encode N) = y.map N.bitSym := by
  rw [List.map_map]
  congr 1
  funext b
  cases b <;> rfl

end BitDFT.DescriptorSlots
open BitDFT.DescriptorSlots BitDFT.DescriptorPlacement BitDFT IntMul

private theorem slot_layout (N : MultitapeTM) (k : ℕ) (hk : 2 ≤ k)
    (cells : Fin (4+(k+3)) → ℕ → N.Sym) (heads : Fin (4+(k+3)) → ℕ)
    (base : RewoundDescriptor.storage.Cfg) (y : List Bool) :
    let start := embed N k cells heads (RewoundDescriptor.initial base y)
    let finish := embed N k cells heads (RewoundDescriptor.final base y)
    start.cells (precisionTape k) = N.tapeOf (y.map N.bitSym) ∧
    start.head (precisionTape k) = y.length+1 ∧
    start.cells (counterTape k) = N.tapeOf [] ∧ start.head (counterTape k) = 0 ∧
    start.cells (templateTape k) = N.tapeOf [] ∧ start.head (templateTape k) = 0 ∧
    finish.cells (precisionTape k) = N.tapeOf (y.map N.bitSym) ∧
    finish.head (precisionTape k) = y.length+1 ∧
    finish.cells (counterTape k) = N.tapeOf (N.sep :: (y.map N.bitSym ++ [N.sep])) ∧
    finish.head (counterTape k) = y.length+1 ∧
    finish.cells (templateTape k) = N.tapeOf (N.sep :: (y.map N.bitSym ++ [N.sep])) ∧
    finish.head (templateTape k) = y.length+1 := by
  have s1 := slot N k cells heads (RewoundDescriptor.initial base y) ⟨1,by decide⟩
  have s2 := slot N k cells heads (RewoundDescriptor.initial base y) ⟨2,by decide⟩
  have s3 := slot N k cells heads (RewoundDescriptor.initial base y) ⟨3,by decide⟩
  have f1 := slot N k cells heads (RewoundDescriptor.final base y) ⟨1,by decide⟩
  have f2 := slot N k cells heads (RewoundDescriptor.final base y) ⟨2,by decide⟩
  have f3 := slot N k cells heads (RewoundDescriptor.final base y) ⟨3,by decide⟩
  dsimp only at s1 s2 s3 f1 f2 f3
  rw [routing_one k hk] at s1 f1
  rw [routing_two k hk] at s2 f2
  rw [routing_three k hk] at s3 f3
  have hf : PreprocessorAlphabet.encode N ∘ DescriptorSetup.machine.bitSym = N.bitSym := by
    funext b
    cases b <;> rfl
  simp [RewoundDescriptor.initial,RewoundDescriptor.final,MachineSequence.leftCfg,
    MachineSequence.rightCfg,RewindTape.frame,DescriptorSetup.initial,DescriptorSetup.final,
    tape_embed,bits,hf,show PreprocessorAlphabet.encode N TapeCopy.Sym.sep = N.sep from rfl] at s1 s2 s3 f1 f2 f3
  exact ⟨s1.1,s1.2,s2.1,s2.2,s3.1,s3.2,f1.1,f1.2,f2.1,f2.2,f3.1,f3.2⟩

private theorem cfg_ext {M : MultitapeTM} (c d : M.Cfg)
    (hs : c.state = d.state) (hc : c.cells = d.cells) (hh : c.head = d.head) : c = d := by
  cases c; cases d; cases hs; cases hc; cases hh; rfl

private theorem reconstruct (N : MultitapeTM) (k : ℕ) (d : (machine N k).Cfg)
    (c : RewoundDescriptor.machine.Cfg) (hs : d.state = c.state)
    (hc : ∀ j : Fin 4,
      d.cells (routing k ⟨j.val,by have := j.isLt; omega⟩) =
        fun p => PreprocessorAlphabet.encode N (c.cells j p))
    (hh : ∀ j : Fin 4,
      d.head (routing k ⟨j.val,by have := j.isLt; omega⟩) = c.head j) :
    embed N k d.cells d.head c = d := by
  apply cfg_ext
  · exact hs.symm
  · funext i
    have he : i = routing k ((routing k).symm i) := (Equiv.apply_symm_apply _ _).symm
    by_cases hj : ((routing k).symm i).val < 4
    · let j : Fin 4 := ⟨((routing k).symm i).val,hj⟩
      have hi : i = routing k ⟨j.val,by have := j.isLt; omega⟩ := he
      rw [hi]
      exact (slot N k d.cells d.head c j).1.trans (hc j).symm
    · have hn : ¬((routing k).symm i).val < (lifted N).k := hj
      simp [embed,TapePermutation.embed,TapeExtension.embed,hn]
  · funext i
    have he : i = routing k ((routing k).symm i) := (Equiv.apply_symm_apply _ _).symm
    by_cases hj : ((routing k).symm i).val < 4
    · let j : Fin 4 := ⟨((routing k).symm i).val,hj⟩
      have hi : i = routing k ⟨j.val,by have := j.isLt; omega⟩ := he
      rw [hi]
      exact (slot N k d.cells d.head c j).2.trans (hh j).symm
    · have hn : ¬((routing k).symm i).val < (lifted N).k := hj
      simp [embed,TapePermutation.embed,TapeExtension.embed,hn]

theorem solution (N : MultitapeTM) (k : ℕ) (hk : 2 ≤ k)
    (d : (machine N k).Cfg) (base : RewoundDescriptor.storage.Cfg) (y : List Bool)
    (hs : d.state = (machine N k).qStart)
    (hroot : d.cells ⟨0,by change 0 < 4+(k+3); omega⟩ = (fun p => PreprocessorAlphabet.encode N (base.cells 0 p)))
    (hrootHead : d.head ⟨0,by change 0 < 4+(k+3); omega⟩ = base.head 0)
    (hp : d.cells (precisionTape k) = N.tapeOf (y.map N.bitSym))
    (hpHead : d.head (precisionTape k) = y.length+1)
    (hc : d.cells (counterTape k) = N.tapeOf []) (hcHead : d.head (counterTape k) = 0)
    (ht : d.cells (templateTape k) = N.tapeOf []) (htHead : d.head (templateTape k) = 0) :
    embed N k d.cells d.head (RewoundDescriptor.initial base y) = d := by
  have hl := slot_layout N k hk d.cells d.head base y
  have cell0 : (embed N k d.cells d.head (RewoundDescriptor.initial base y)).cells ⟨0,by change 0 < 4+(k+3); omega⟩ =
      d.cells ⟨0,by change 0 < 4+(k+3); omega⟩ := by
    have h := (slot N k d.cells d.head (RewoundDescriptor.initial base y) ⟨0,by decide⟩).1
    dsimp only at h
    rw [routing_zero] at h
    simpa [RewoundDescriptor.initial,MachineSequence.leftCfg,RewindTape.frame,DescriptorSetup.initial] using h.trans hroot.symm
  have head0 : (embed N k d.cells d.head (RewoundDescriptor.initial base y)).head ⟨0,by change 0 < 4+(k+3); omega⟩ =
      d.head ⟨0,by change 0 < 4+(k+3); omega⟩ := by
    have h := (slot N k d.cells d.head (RewoundDescriptor.initial base y) ⟨0,by decide⟩).2
    dsimp only at h
    rw [routing_zero] at h
    simpa [RewoundDescriptor.initial,MachineSequence.leftCfg,RewindTape.frame,DescriptorSetup.initial] using h.trans hrootHead.symm
  apply reconstruct N k d (RewoundDescriptor.initial base y) hs
  · intro j
    have hslot := (slot N k d.cells d.head (RewoundDescriptor.initial base y) j).1
    apply Eq.trans _ hslot
    fin_cases j
    · simpa only [routing_zero] using cell0.symm
    · simpa only [routing_one k hk] using hp.trans hl.1.symm
    · simpa only [routing_two k hk] using hc.trans hl.2.2.1.symm
    · simpa only [routing_three k hk] using ht.trans hl.2.2.2.2.1.symm
  · intro j
    have hslot := (slot N k d.cells d.head (RewoundDescriptor.initial base y) j).2
    apply Eq.trans _ hslot
    fin_cases j
    · simpa only [routing_zero] using head0.symm
    · simpa only [routing_one k hk] using hpHead.trans hl.2.1.symm
    · simpa only [routing_two k hk] using hcHead.trans hl.2.2.2.1.symm
    · simpa only [routing_three k hk] using htHead.trans hl.2.2.2.2.2.1.symm
