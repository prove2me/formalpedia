-- Prove2me | solution 1 for BitDFT.descriptor_slots
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T18:19:48.371276+00:00
-- url     : https://prove2.me/submissions/7b879495-e365-4c92-abdd-07b4f0b82c96

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

theorem solution (N : MultitapeTM) (k : ℕ) (hk : 2 ≤ k)
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
