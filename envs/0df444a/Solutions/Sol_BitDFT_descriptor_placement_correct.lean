-- Prove2me | solution 1 for BitDFT.descriptor_placement_correct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T18:16:50.423313+00:00
-- url     : https://prove2.me/submissions/23f55dfd-0b70-455f-92c4-a6de1b1cdcf2

import Definitions.Def_BitDFT_DescriptorPlacement
import Theorems.Thm_BitDFT_alphabet_embedding_correct
import Theorems.Thm_BitDFT_tape_extension_correct
import Theorems.Thm_BitDFT_tape_permutation_run
import Theorems.Thm_BitDFT_rewound_descriptor_correct

namespace BitDFT.DescriptorPlacement
open IntMul

theorem run_embed (N : MultitapeTM) (k : ℕ)
    (cells : Fin (4+(k+3)) → ℕ → N.Sym) (heads : Fin (4+(k+3)) → ℕ)
    (c : RewoundDescriptor.machine.Cfg) (t : ℕ) :
    (machine N k).step^[t] (embed N k cells heads c) =
      embed N k cells heads (RewoundDescriptor.machine.step^[t] c) := by
  unfold embed
  rw [BitDFT.tape_permutation_run,
    (BitDFT.tape_extension_correct (lifted N) (k+3)).1,
    (BitDFT.alphabet_embedding_correct RewoundDescriptor.machine N (alphabetMap N)).1]

theorem parked (N : MultitapeTM) (k : ℕ)
    (cells : Fin (4+(k+3)) → ℕ → N.Sym) (heads : Fin (4+(k+3)) → ℕ)
    (c : RewoundDescriptor.machine.Cfg) (i : Fin (4+(k+3)))
    (hi : 4 ≤ ((routing k).symm i).val) :
    (embed N k cells heads c).cells i = cells i ∧
    (embed N k cells heads c).head i = heads i := by
  have hn : ¬((routing k).symm i).val < (lifted N).k := by change ¬_ < 4; omega
  simp [embed,TapePermutation.embed,TapeExtension.embed,hn]

end BitDFT.DescriptorPlacement
open BitDFT.DescriptorPlacement BitDFT IntMul

theorem solution (N : MultitapeTM) (k : ℕ)
    (cells : Fin (4+(k+3)) → ℕ → N.Sym) (heads : Fin (4+(k+3)) → ℕ)
    (base : RewoundDescriptor.storage.Cfg) (y : List Bool) :
    ∃ t : ℕ, t ≤ 2*y.length+6 ∧
      (machine N k).step^[t] (embed N k cells heads (RewoundDescriptor.initial base y)) =
        embed N k cells heads (RewoundDescriptor.final base y) ∧
      ∀ i : Fin (4+(k+3)), 4 ≤ ((routing k).symm i).val →
        ((machine N k).step^[t] (embed N k cells heads (RewoundDescriptor.initial base y))).cells i = cells i ∧
        ((machine N k).step^[t] (embed N k cells heads (RewoundDescriptor.initial base y))).head i = heads i := by
  obtain ⟨t,ht,hr⟩ := BitDFT.rewound_descriptor_correct base y
  refine ⟨t,ht,?_,?_⟩
  · rw [run_embed,hr]
  · intro i hi
    rw [run_embed,hr]
    exact parked N k cells heads _ i hi
