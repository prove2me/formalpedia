-- Prove2me | solution 1 for BookProof.ChapterGaugeComprehensiveFixing.orbitRepresentatives_isComprehensiveGaugeFixing
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:26:56.765618+00:00
-- url     : https://prove2.me/submissions/ac2d6876-e047-4286-9f51-5c60499d1e0c

-- Generated from ChapterGaugeComprehensiveFixing.lean — solution of BookProof.ChapterGaugeComprehensiveFixing.orbitRepresentatives_isComprehensiveGaugeFixing
import Mathlib
import Definitions.Def_ChapterGaugeComprehensiveFixing
open BookProof.ChapterGaugeComprehensiveFixing




open BookProof.ChapterGaugeIncompleteFixing

variable {X : Type*} (G : Type*) [Group G] [MulAction G X]

set_option maxHeartbeats 1000000 in
theorem solution :
    IsComprehensiveGaugeFixing G (orbitRepresentatives (X := X) G) := by

  intro x
  refine ⟨(Quotient.mk (MulAction.orbitRel G X) x).out, ⟨_, rfl⟩, ?_⟩
  have h : Quotient.mk (MulAction.orbitRel G X)
      (Quotient.mk (MulAction.orbitRel G X) x).out
      = Quotient.mk (MulAction.orbitRel G X) x := Quotient.out_eq _
  obtain ⟨g, hg⟩ := Quotient.exact h
  exact ⟨g⁻¹, by rw [← hg, inv_smul_smul]⟩
