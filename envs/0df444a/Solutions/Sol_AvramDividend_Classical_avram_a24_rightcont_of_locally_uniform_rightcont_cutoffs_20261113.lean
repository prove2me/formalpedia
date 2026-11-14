-- Prove2me | solution 1 for AvramDividend.Classical.avram_a24_rightcont_of_locally_uniform_rightcont_cutoffs_20261113
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T23:53:08.111864+00:00
-- url     : https://prove2.me/submissions/c03a5a11-01ab-4124-8914-aac672de0ac6

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter Set Topology
open scoped NNReal ENNReal
noncomputable section

/-- A locally uniform limit of functions right-continuous at the same time is right-continuous there. -/
theorem solution
    (F : ℕ → ℝ≥0 → ℝ) (g : ℝ≥0 → ℝ) (t : ℝ≥0)
    (hRight : ∀ n : ℕ, ContinuousWithinAt (F n) (Ici t) t)
    (hUniform : TendstoLocallyUniformlyOn F g atTop (Ici t)) :
    ContinuousWithinAt g (Ici t) t := by
  apply continuousWithinAt_of_locally_uniform_approx_of_continuousWithinAt
    (show t ∈ Ici t from le_refl t)
  intro u hu
  obtain ⟨v, hv, hEvent⟩ := hUniform u hu t (show t ∈ Ici t from le_refl t)
  obtain ⟨n, hn⟩ := hEvent.exists
  exact ⟨v, hv, F n, hRight n, hn⟩
