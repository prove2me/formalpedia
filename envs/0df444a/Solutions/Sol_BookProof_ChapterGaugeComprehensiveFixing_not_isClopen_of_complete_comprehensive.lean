-- Prove2me | solution 1 for BookProof.ChapterGaugeComprehensiveFixing.not_isClopen_of_complete_comprehensive
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:28:14.839223+00:00
-- url     : https://prove2.me/submissions/daa4651d-3fa4-454d-bc1b-1c8ba965d0c9

-- Generated from ChapterGaugeComprehensiveFixing.lean — solution of BookProof.ChapterGaugeComprehensiveFixing.not_isClopen_of_complete_comprehensive
import Mathlib
import Definitions.Def_ChapterGaugeComprehensiveFixing
open BookProof.ChapterGaugeComprehensiveFixing




open BookProof.ChapterGaugeIncompleteFixing

variable {X : Type*} (G : Type*) [Group G] [MulAction G X]
variable {X : Type*} {G : Type*} [Group G] [MulAction G X] {S : Set X}
variable {X : Type*} [TopologicalSpace X] {G : Type*} [Group G] [MulAction G X]

set_option maxHeartbeats 1000000 in
theorem solution [PreconnectedSpace X] [Nonempty X]
    [Nontrivial G] {S : Set X}
    (hcomp : IsComprehensiveGaugeFixing G S) (hcompl : IsCompleteGaugeFixing' G S)
    (hfree : MovesEveryPointOfSpectrum G X) :
    ¬ IsClopen S := by

  intro hclopen
  obtain ⟨x⟩ := ‹Nonempty X›
  obtain ⟨s, hsS, -, -⟩ := hcomp x
  obtain ⟨h, hh⟩ := exists_ne (1 : G)
  have hne : S.Nonempty := ⟨s, hsS⟩
  have hnotmem : h • s ∉ S := fun hmem => hfree h hh s (hcompl s hsS (h • s) hmem h rfl).symm
  rcases isClopen_iff.mp hclopen with hempty | huniv
  · exact absurd hempty (Set.nonempty_iff_ne_empty.mp hne)
  · exact hnotmem (huniv ▸ Set.mem_univ _)
