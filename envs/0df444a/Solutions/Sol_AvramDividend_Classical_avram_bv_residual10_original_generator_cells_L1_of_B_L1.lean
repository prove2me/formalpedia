-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_residual10_original_generator_cells_L1_of_B_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T22:55:51.366036+00:00
-- url     : https://prove2.me/submissions/48bdfbd9-ac18-43f3-92d3-f6a7df8edfb6

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bv_residual10_original_weighted_grid_residual_zero_ae

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Integrability of the actual compensated BV grid budget transfers to its
generator-cell part because the original weighted residual vanishes a.e. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (u : ℕ → ℕ → ℝ≥0) (A : ℕ → Ω → ℕ → ℝ)
    (B G : ℕ → Ω → ℝ)
    (hB : ∀ n ω,
      let J : ℝ≥0 → ℝ := fun t =>
        ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
        else 0
      let R : ℝ≥0 → ℝ := fun t =>
        ((t : ℝ) * X.drift - X.X t ω) - J t
      B n ω = G n ω +
        ∑ i ∈ Finset.range (n + 1),
          A n ω i * (R (u n i) - R (u n (i + 1))))
    (hBI : ∀ n, Integrable (B n) P) :
    ∀ n, Integrable (G n) P ∧ B n =ᵐ[P] G n := by
  have hzero := avram_bv_residual10_original_weighted_grid_residual_zero_ae
    X hX hBV u A
  intro n
  have heq : B n =ᵐ[P] G n := by
    filter_upwards [hzero] with ω hz
    let J : ℝ≥0 → ℝ := fun t =>
      ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
        Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
      else 0
    let R : ℝ≥0 → ℝ := fun t =>
      ((t : ℝ) * X.drift - X.X t ω) - J t
    have hs : (∑ i ∈ Finset.range (n + 1),
        A n ω i * (R (u n i) - R (u n (i + 1)))) = 0 := hz n
    have hb : B n ω = G n ω +
        ∑ i ∈ Finset.range (n + 1),
          A n ω i * (R (u n i) - R (u n (i + 1))) := hB n ω
    rw [hs, add_zero] at hb
    exact hb
  exact ⟨(hBI n).congr heq, heq⟩
