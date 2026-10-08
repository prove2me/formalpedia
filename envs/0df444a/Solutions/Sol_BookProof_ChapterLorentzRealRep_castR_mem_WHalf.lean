-- Prove2me | solution 1 for BookProof.ChapterLorentzRealRep.castR_mem_WHalf
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-07T16:56:11.274108+00:00
-- url     : https://prove2.me/submissions/9b814645-c72a-4286-8fa3-413ee8922902

-- Generated from ChapterLorentzRealRep.lean — solution of BookProof.ChapterLorentzRealRep.castR_mem_WHalf
import Mathlib
import Definitions.Def_ChapterLorentzRealRep
open BookProof.ChapterLorentzRealRep



open Matrix


open BookProof.ChapterA3 BookProof.ChapterPinOmega

set_option maxHeartbeats 1000000 in
theorem solution : ∀ M ∈ SBHalf, castR M ∈ WHalf := by

  intro M hM
  unfold SBHalf at hM
  simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and] at hM;
  rcases hM with ( ⟨ i, rfl ⟩ | ⟨ i, rfl ⟩ )
  · exact Submodule.subset_span ⟨ i, rfl ⟩
  · rw [show castR (-bHalf i) = -castR (bHalf i) by ext; simp [castR]]
    exact Submodule.neg_mem _ (Submodule.subset_span (Set.mem_range_self i))
