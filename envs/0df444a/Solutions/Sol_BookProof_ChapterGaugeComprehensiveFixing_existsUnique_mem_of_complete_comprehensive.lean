-- Prove2me | solution 1 for BookProof.ChapterGaugeComprehensiveFixing.existsUnique_mem_of_complete_comprehensive
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:27:11.858579+00:00
-- url     : https://prove2.me/submissions/9767db4e-3355-4369-b274-cfad1ec1de55

-- Generated from ChapterGaugeComprehensiveFixing.lean — solution of BookProof.ChapterGaugeComprehensiveFixing.existsUnique_mem_of_complete_comprehensive
import Mathlib
import Definitions.Def_ChapterGaugeComprehensiveFixing
open BookProof.ChapterGaugeComprehensiveFixing




open BookProof.ChapterGaugeIncompleteFixing

variable {X : Type*} (G : Type*) [Group G] [MulAction G X]
variable {X : Type*} {G : Type*} [Group G] [MulAction G X] {S : Set X}

set_option maxHeartbeats 1000000 in
theorem solution
    (hcomp : IsComprehensiveGaugeFixing G S) (hcompl : IsCompleteGaugeFixing' G S)
    (x : X) : ∃! s : X, s ∈ S ∧ ∃ g : G, g • s = x := by

  obtain ⟨s, hsS, g, hgs⟩ := hcomp x
  refine ⟨s, ⟨hsS, g, hgs⟩, ?_⟩
  rintro t ⟨htS, h, hht⟩
  exact hcompl t htS s hsS (g⁻¹ * h) (by rw [mul_smul, hht, ← hgs, inv_smul_smul])
