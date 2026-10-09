-- Prove2me | solution 1 for BookProof.ChapterGaugeIncompleteFixing.no_gauge_invariant_point
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:31:01.28585+00:00
-- url     : https://prove2.me/submissions/92050ca0-bc02-4f9d-a2c8-83e53337fcfe

-- Generated from ChapterGaugeIncompleteFixing.lean — solution of BookProof.ChapterGaugeIncompleteFixing.no_gauge_invariant_point
import Mathlib
import Definitions.Def_ChapterGaugeIncompleteFixing
open BookProof.ChapterGaugeIncompleteFixing



open scoped InnerProductSpace

variable {X : Type*}
variable (G : Type*) [Group G] [MulAction G X]

set_option maxHeartbeats 1000000 in
theorem solution [Nontrivial G] (h : MovesEveryPointOfSpectrum G X)
    (x : X) : ∃ g : G, g • x ≠ x := by

  obtain ⟨g, hg⟩ := exists_ne (1 : G)
  exact ⟨g, h g hg x⟩
