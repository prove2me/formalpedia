-- Prove2me | solution 1 for BookProof.ChapterLorentzRealRep.castR_mem_WPs
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T20:55:51.920983+00:00
-- url     : https://prove2.me/submissions/f9ac9eda-de84-4b32-b4af-d5bde0f450af

-- Generated from ChapterLorentzRealRep.lean — solution of BookProof.ChapterLorentzRealRep.castR_mem_WPs
import Mathlib
import Definitions.Def_ChapterLorentzRealRep
import Definitions.Def_ChapterA3
import Definitions.Def_ChapterPinOmega
open BookProof.ChapterLorentzRealRep



open Matrix


open BookProof.ChapterA3 BookProof.ChapterPinOmega

set_option maxHeartbeats 1000000 in
theorem solution : ∀ M ∈ SBPs, castR M ∈ WPs := by

  intro M hM
  unfold SBPs at hM
  simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and] at hM
  rcases hM with ⟨i, rfl⟩ | ⟨i, rfl⟩;
  · exact Submodule.subset_span ⟨ i, rfl ⟩;
  · rw [show castR (-bPs i) = -castR (bPs i) by ext; simp [castR]]
    exact Submodule.neg_mem _ (Submodule.subset_span (Set.mem_range_self i))
