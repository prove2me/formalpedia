-- Prove2me | solution 1 for BookProof.ChapterGaugeIncompleteFixing.unconstrained_gauge_fixing_incomplete
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:30:01.201268+00:00
-- url     : https://prove2.me/submissions/0def9195-8b69-4bf1-a98e-c7619ef2203c

-- Generated from ChapterGaugeIncompleteFixing.lean — solution of BookProof.ChapterGaugeIncompleteFixing.unconstrained_gauge_fixing_incomplete
import Mathlib
import Definitions.Def_ChapterGaugeIncompleteFixing
open BookProof.ChapterGaugeIncompleteFixing



open scoped InnerProductSpace

variable {X : Type*}
variable (G : Type*) [Group G] [MulAction G X]

set_option maxHeartbeats 1000000 in
theorem solution [Nontrivial G] [Nonempty X]
    (h : MovesEveryPointOfSpectrum G X) :
    ¬ IsCompleteGaugeFixing' G (Set.univ : Set X) := by

  intro hcomp
  obtain ⟨g, hg⟩ := exists_ne (1 : G)
  obtain ⟨x⟩ := ‹Nonempty X›
  exact h g hg x (hcomp x (Set.mem_univ x) (g • x) (Set.mem_univ _) g rfl).symm
