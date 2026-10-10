-- Prove2me | solution 1 for BookProof.ChapterLorentzRealRepFull.castR_mem_WTwo
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T21:07:30.105989+00:00
-- url     : https://prove2.me/submissions/75b5b6e1-6f8e-4c52-a7e1-f1411131b1e1

-- Generated from ChapterLorentzRealRepFull.lean — solution of BookProof.ChapterLorentzRealRepFull.castR_mem_WTwo
import Mathlib
import Definitions.Def_ChapterLorentzRealRepFull
import Definitions.Def_ChapterA3
import Definitions.Def_ChapterPinOmega
import Definitions.Def_ChapterLorentzRealRepSum
import Definitions.Def_ChapterLorentzRealRep
open BookProof.ChapterLorentzRealRepFull



open Matrix


open BookProof.ChapterA3 BookProof.ChapterPinOmega BookProof.ChapterLorentzRealRep
open BookProof.ChapterLorentzRealRepSum
open Module

set_option maxHeartbeats 1000000 in
theorem solution : ∀ M ∈ SW2, castR M ∈ WTwo := by

  intro M hM
  simp only [SW2, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and] at hM
  obtain ⟨i, rfl⟩ | ⟨i, rfl⟩ := hM <;> simp only [WTwo]
  · exact Submodule.subset_span ⟨i, rfl⟩
  · rw [show castR (-w2 i) = -castR (w2 i) by ext; simp [castR]]
    exact Submodule.neg_mem _ <| Submodule.subset_span <| Set.mem_range_self _
