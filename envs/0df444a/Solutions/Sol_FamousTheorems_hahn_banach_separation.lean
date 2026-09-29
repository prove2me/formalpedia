-- Prove2me | solution 1 for FamousTheorems.hahn_banach_separation
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T02:17:46.165629+00:00
-- url     : https://prove2.me/submissions/fc70a650-79c5-4f7f-91e4-bc836b7996bf

import Mathlib

theorem solution {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E] [IsTopologicalAddGroup E]
    [ContinuousSMul ℝ E] {s t : Set E} (hs₁ : Convex ℝ s) (hs₂ : IsOpen s) (ht : Convex ℝ t)
    (disj : Disjoint s t) :
    ∃ (f : StrongDual ℝ E) (u : ℝ), (∀ a ∈ s, f a < u) ∧ ∀ b ∈ t, u ≤ f b :=
  geometric_hahn_banach_open hs₁ hs₂ ht disj
