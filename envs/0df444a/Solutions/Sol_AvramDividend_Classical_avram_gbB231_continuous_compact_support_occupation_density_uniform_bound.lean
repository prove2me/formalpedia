-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB231_continuous_compact_support_occupation_density_uniform_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T10:05:31.093559+00:00
-- url     : https://prove2.me/submissions/291d9eb2-3248-4a9e-bbea-f813c924ef63

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
noncomputable section

/-- Compact continuity gives a finite global bound for a compactly supported occupation density. -/
theorem solution
    (ℓ : ℝ → ℝ) (R : ℝ)
    (hContinuous : Continuous ℓ)
    (hNonneg : ∀ z, 0 ≤ ℓ z)
    (hSupport : ∀ z, z ∉ Set.Icc (-R) R → ℓ z = 0) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ z : ℝ, ℓ z ≤ B := by
  have hContOn : ContinuousOn ℓ (Set.Icc (-R) R) :=
    hContinuous.continuousOn
  obtain ⟨C, hC⟩ :=
    (isCompact_Icc : IsCompact (Set.Icc (-R) R)).exists_bound_of_continuousOn
      (f := ℓ) hContOn
  refine ⟨max 0 C, le_max_left _ _, ?_⟩
  intro z
  by_cases hz : z ∈ Set.Icc (-R) R
  · have hnorm : ‖ℓ z‖ = ℓ z := by
      rw [Real.norm_eq_abs, abs_of_nonneg (hNonneg z)]
    exact (hnorm ▸ hC z hz).trans (le_max_right _ _)
  · rw [hSupport z hz]
    exact le_max_left _ _
