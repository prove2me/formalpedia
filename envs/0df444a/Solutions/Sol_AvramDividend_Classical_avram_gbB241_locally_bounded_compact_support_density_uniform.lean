-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB241_locally_bounded_compact_support_density_uniform
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T10:13:57.822048+00:00
-- url     : https://prove2.me/submissions/c08d7635-a422-44f8-b62d-5b9693dbbf68

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
noncomputable section

/-- Local spatial boundedness plus compact support bounds the entire occupation density. -/
theorem solution
    (ℓ : ℝ → ℝ) (R : ℝ)
    (hLocal : ∀ z : ℝ,
      ∃ U ∈ 𝓝 z, Bornology.IsBounded (ℓ '' U))
    (hNonneg : ∀ z : ℝ, 0 ≤ ℓ z)
    (hSupport : ∀ z, z ∉ Set.Icc (-R) R → ℓ z = 0) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ z : ℝ, ℓ z ≤ B := by
  have hBound : Bornology.IsBounded (ℓ '' Set.Icc (-R) R) :=
    Bornology.isBounded_image_of_isLocallyBounded_of_isCompact
      (isCompact_Icc : IsCompact (Set.Icc (-R) R)) hLocal
  obtain ⟨C, hC⟩ := hBound.exists_norm_le
  refine ⟨max 0 C, le_max_left _ _, ?_⟩
  intro z
  by_cases hz : z ∈ Set.Icc (-R) R
  · have hnorm : ‖ℓ z‖ = ℓ z := by
      rw [Real.norm_eq_abs, abs_of_nonneg (hNonneg z)]
    exact (hnorm ▸ hC (ℓ z) ⟨z, hz, rfl⟩).trans (le_max_right _ _)
  · rw [hSupport z hz]
    exact le_max_left _ _
