-- Prove2me | solution 1 for BookProof.ChapterGaugeIncompleteFixing.remnant_faithful
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:30:37.286955+00:00
-- url     : https://prove2.me/submissions/6c0bab88-3f80-4339-8e6b-37a55712f29c

-- Generated from ChapterGaugeIncompleteFixing.lean — solution of BookProof.ChapterGaugeIncompleteFixing.remnant_faithful
import Mathlib
import Definitions.Def_ChapterGaugeIncompleteFixing
open BookProof.ChapterGaugeIncompleteFixing



open scoped InnerProductSpace

variable {X : Type*}
variable (G : Type*) [Group G] [MulAction G X]

set_option maxHeartbeats 1000000 in
theorem solution [Nonempty X] (h : MovesEveryPointOfSpectrum G X)
    {g : G} (hg : ∀ x : X, g • x = x) : g = 1 := by

  by_contra hne
  obtain ⟨x⟩ := ‹Nonempty X›
  exact h g hne x (hg x)
