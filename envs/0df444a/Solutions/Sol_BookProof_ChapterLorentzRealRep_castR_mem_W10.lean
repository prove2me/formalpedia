-- Prove2me | solution 1 for BookProof.ChapterLorentzRealRep.castR_mem_W10
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-07T16:56:23.578282+00:00
-- url     : https://prove2.me/submissions/f0dc67a9-c582-4442-b018-8dbd5420aecf

-- Generated from ChapterLorentzRealRep.lean — solution of BookProof.ChapterLorentzRealRep.castR_mem_W10
import Mathlib
import Definitions.Def_ChapterLorentzRealRep
open BookProof.ChapterLorentzRealRep



open Matrix


open BookProof.ChapterA3 BookProof.ChapterPinOmega

set_option maxHeartbeats 1000000 in
theorem solution : ∀ M ∈ SB10, castR M ∈ W10 := by

  -- By definition of `SB10`, every element is either in the image of `b10` or the image of `-b10`.
  intro M hM
  simp only [SB10, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and] at hM;
  obtain ⟨i, rfl⟩ | ⟨i, rfl⟩ := hM <;> simp only [W10]
  · exact Submodule.subset_span ⟨i, rfl⟩
  · rw [show castR (-b10 i) = -castR (b10 i) by ext; simp [castR]]
    exact Submodule.neg_mem _ <| Submodule.subset_span <| Set.mem_range_self _
