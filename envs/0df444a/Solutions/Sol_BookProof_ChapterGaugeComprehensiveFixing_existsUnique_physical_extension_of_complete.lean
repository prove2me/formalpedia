-- Prove2me | solution 1 for BookProof.ChapterGaugeComprehensiveFixing.existsUnique_physical_extension_of_complete
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:27:25.663656+00:00
-- url     : https://prove2.me/submissions/ec1091fa-a96e-4c2a-9adb-79103b4d0e9e

-- Generated from ChapterGaugeComprehensiveFixing.lean — solution of BookProof.ChapterGaugeComprehensiveFixing.existsUnique_physical_extension_of_complete
import Mathlib
import Definitions.Def_ChapterGaugeComprehensiveFixing
import Theorems.Thm_BookProof_ChapterGaugeComprehensiveFixing_exists_physical_extension_of_complete
import Theorems.Thm_BookProof_ChapterGaugeIncompleteFixing_physical_ext_of_comprehensive
open BookProof.ChapterGaugeComprehensiveFixing




open BookProof.ChapterGaugeIncompleteFixing

variable {X : Type*} (G : Type*) [Group G] [MulAction G X]
variable {X : Type*} {G : Type*} [Group G] [MulAction G X] {S : Set X}

set_option maxHeartbeats 1000000 in
theorem solution
    (hcomp : IsComprehensiveGaugeFixing G S) (hcompl : IsCompleteGaugeFixing' G S)
    (h : X → ℝ) :
    ∃! f : X → ℝ, IsPhysicalObservable G f ∧ ∀ s ∈ S, f s = h s := by

  obtain ⟨f, hf, hfS⟩ := exists_physical_extension_of_complete hcomp hcompl h
  refine ⟨f, ⟨hf, hfS⟩, ?_⟩
  rintro f' ⟨hf_prime, hf'S⟩
  exact physical_ext_of_comprehensive G hcomp hf_prime hf (fun s hs => by rw [hf'S s hs, hfS s hs])
