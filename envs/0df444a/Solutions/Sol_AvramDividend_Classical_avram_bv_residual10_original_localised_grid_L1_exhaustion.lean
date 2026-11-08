-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_residual10_original_localised_grid_L1_exhaustion
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T14:18:37.459406+00:00
-- url     : https://prove2.me/submissions/3fbcc48a-896f-4551-981a-f2108109fe71

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bv_residual10_finite_coordinate_event_measurable
import Theorems.Thm_AvramDividend_Classical_avram_bv_residual10_finite_coordinate_event_exhaustion
import Theorems.Thm_AvramDividend_Classical_avram_bv_residual10_original_compact_localised_R_mesh_L1

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Exact original BV physical-grid residual sums admit an explicit measurable
exhaustion by finite-coordinate events, integrable at each localisation level. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (T : ℝ≥0)
    (u : ℕ → ℕ → ℝ≥0) (n : ℕ)
    (hu : ∀ i, i < n + 1 → u n i ≤ u n (i + 1))
    (hu0 : u n 0 = 0) (huT : u n (n + 1) ≤ T)
    (a : Ω → ℕ → ℝ) (ha : ∀ i, Measurable (fun ω => a ω i)) :
    ∃ A : ℕ → Set Ω,
      (∀ k, MeasurableSet (A k)) ∧
      (∀ ω, ∀ᶠ k in atTop, ω ∈ A k) ∧
      (∀ k, Integrable (fun ω =>
        if ω ∈ A k then
          let J : ℝ≥0 → ℝ := fun t =>
            ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
              Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω else 0
          let R : ℝ≥0 → ℝ := fun t =>
            ((t : ℝ) * X.drift - X.X t ω) - J t
          ∑ i ∈ Finset.range (n + 1),
            a ω i * (R (u n i) - R (u n (i + 1)))
        else 0) P) := by
  classical
  let A : ℕ → Set Ω := fun k =>
    {ω | ∀ i ∈ Finset.range (n + 1), abs (a ω i) ≤ (k : ℝ)}
  refine ⟨A, ?_, ?_, ?_⟩
  · intro k
    exact avram_bv_residual10_finite_coordinate_event_measurable n a ha k
  · intro ω
    obtain ⟨N, hN⟩ := avram_bv_residual10_finite_coordinate_event_exhaustion n a ω
    exact eventually_atTop.mpr ⟨N, hN⟩
  · intro k
    apply avram_bv_residual10_original_compact_localised_R_mesh_L1
      X hX hBV T u n hu hu0 huT a ha (A k)
        (avram_bv_residual10_finite_coordinate_event_measurable n a ha k)
        (k : ℝ) (Nat.cast_nonneg k)
    intro ω hω i hi
    exact hω i hi
