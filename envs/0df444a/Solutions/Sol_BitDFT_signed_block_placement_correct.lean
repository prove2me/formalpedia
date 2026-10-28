-- Prove2me | solution 1 for BitDFT.signed_block_placement_correct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T18:52:12.474051+00:00
-- url     : https://prove2.me/submissions/f0cc3a30-fd52-48ab-8e39-b60e1a1e7a72

import Definitions.Def_BitDFT_SignedBlockPlacement
import Theorems.Thm_BitDFT_alphabet_embedding_correct
import Theorems.Thm_BitDFT_tape_extension_correct
import Theorems.Thm_BitDFT_tape_permutation_run
import Theorems.Thm_BitDFT_work_signed_block_correct

namespace BitDFT.SignedBlockPlacement
open IntMul

theorem run_embed (N : MultitapeTM) (k : ℕ)
    (cells : Fin (5+(k+3)) → ℕ → N.Sym) (heads : Fin (5+(k+3)) → ℕ)
    (c : storage.Cfg) (t : ℕ) :
    (machine N k).step^[t] (embed N k cells heads c) =
      embed N k cells heads (storage.step^[t] c) := by
  unfold embed
  rw [BitDFT.tape_permutation_run,
    (BitDFT.tape_extension_correct (lifted N) (k+3)).1,
    (BitDFT.alphabet_embedding_correct storage N (alphabetMap N)).1]

theorem parked (N : MultitapeTM) (k : ℕ)
    (cells : Fin (5+(k+3)) → ℕ → N.Sym) (heads : Fin (5+(k+3)) → ℕ)
    (c : storage.Cfg) (i : Fin (5+(k+3)))
    (hi : 5 ≤ ((routing k).symm i).val) :
    (embed N k cells heads c).cells i = cells i ∧
    (embed N k cells heads c).head i = heads i := by
  have hn : ¬((routing k).symm i).val < (lifted N).k := by change ¬_ < 5; omega
  simp [embed,TapePermutation.embed,TapeExtension.embed,hn]

end BitDFT.SignedBlockPlacement
open BitDFT.SignedBlockPlacement BitDFT IntMul

theorem solution (N : MultitapeTM) (k : ℕ)
    (cells : Fin (5+(k+3)) → ℕ → N.Sym) (heads : Fin (5+(k+3)) → ℕ)
    (rootCells : ℕ → TapeCopy.Sym) (rootHead : ℕ)
    (pre out : List Bool) (sign : Bool) (x y : List Bool) (hx : val y+1 ≤ x.length) :
    let start := WorkRelocation.embed SignedBlock.machine rootCells rootHead
      (SignedBlock.initial pre out sign x y)
    let finish := WorkRelocation.embed SignedBlock.machine rootCells rootHead
      (SignedBlock.final pre out sign x y)
    ∃ t : ℕ, t ≤ 6*(val y+1)+4*y.length+4 ∧
      (machine N k).step^[t] (embed N k cells heads start) = embed N k cells heads finish ∧
      ∀ i : Fin (5+(k+3)), 5 ≤ ((routing k).symm i).val →
        ((machine N k).step^[t] (embed N k cells heads start)).cells i = cells i ∧
        ((machine N k).step^[t] (embed N k cells heads start)).head i = heads i := by
  dsimp only
  obtain ⟨t,ht,hr⟩ := BitDFT.work_signed_block_correct rootCells rootHead pre out sign x y hx
  refine ⟨t,ht,?_,?_⟩
  · rw [run_embed,hr]
  · intro i hi
    rw [run_embed,hr]
    exact parked N k cells heads _ i hi
