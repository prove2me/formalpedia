-- Prove2me | solution 1 for BitDFT.signed_block_final_slots
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T19:04:39.399902+00:00
-- url     : https://prove2.me/submissions/ad0be44d-1127-4471-89ee-dff5a2bc11a1

import Definitions.Def_BitDFT_SignedBlockPlacement
import Mathlib.Tactic
set_option maxHeartbeats 1000000
namespace BitDFT.SignedBlockFinalSlots
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

end BitDFT.SignedBlockFinalSlots
open BitDFT.SignedBlockFinalSlots BitDFT.SignedBlockPlacement BitDFT IntMul

theorem solution (N : MultitapeTM) (k : ℕ)
    (cells : Fin (5+(k+3)) → ℕ → N.Sym) (heads : Fin (5+(k+3)) → ℕ)
    (rootCells : ℕ → TapeCopy.Sym) (rootHead : ℕ)
    (pre out : List Bool) (sign : Bool) (x y : List Bool) :
    let start := embed N k cells heads (WorkRelocation.embed SignedBlock.machine rootCells rootHead
      (SignedBlock.final pre out sign x y))
    start.cells ⟨1,by change 1 < 5+(k+3); omega⟩ = N.tapeOf ((pre++sign::x).map N.bitSym) ∧
    start.head ⟨1,by change 1 < 5+(k+3); omega⟩ = pre.length+val y+3 ∧
    start.cells (scratchTape k) = N.tapeOf ((out++sign::x.take (val y+1)).map N.bitSym) ∧
    start.head (scratchTape k) = out.length+val y+3 ∧
    start.cells (counterTape k) = N.tapeOf (N.sep :: (y.map N.bitSym ++ [N.sep])) ∧
    start.head (counterTape k) = y.length+1 ∧
    start.cells (templateTape k) = N.tapeOf (N.sep :: (y.map N.bitSym ++ [N.sep])) ∧
    start.head (templateTape k) = y.length+1 := by
  let c := WorkRelocation.embed SignedBlock.machine rootCells rootHead (SignedBlock.final pre out sign x y)
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
  simp [c,WorkRelocation.embed,WorkRelocation.innerTape,SignedBlock.final,
    MachineSequence.rightCfg,SignedBlock.blockFrame,CountedBlock.frame,
    List.append_assoc,Nat.add_assoc,tape_embed,bits,hf,hsign,show PreprocessorAlphabet.encode N TapeCopy.Sym.sep = N.sep from rfl] at s1 s2 s3 s4 ⊢
  exact ⟨s1.1,by omega,s2.1,by omega,s3.1,s3.2,s4.1,s4.2⟩
