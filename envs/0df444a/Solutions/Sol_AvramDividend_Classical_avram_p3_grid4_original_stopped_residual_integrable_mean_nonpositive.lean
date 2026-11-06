-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_grid4_original_stopped_residual_integrable_mean_nonpositive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T00:07:45.35626+00:00
-- url     : https://prove2.me/submissions/92fa8510-cca8-477c-a80b-fa94e4faca66

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_original_uniform_ruin_stopped_residual_nonpositive
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- Original stopped BV residual L1 sign is inherited by expectation. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (T : ℝ≥0) (m : ℕ)
    (W : ℕ → Ω → ℝ) (hW : ∀ ω i, 0 ≤ W i ω) :
    let Z : Ω → ℝ := fun ω =>
        let u : ℕ → ℝ≥0 := fun i =>
          ((min i (m + 1) : ℕ) : ℝ≥0) * (T / (m + 1))
        let τ : Ω → ℝ≥0 := fun ξ =>
          (min (ruinTime X x D ξ) (T : ℝ≥0∞)).toNNReal
        let R : ℝ≥0 → ℝ := fun t =>
          ((t : ℝ) * X.drift - X.X t ω) -
            (∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
              Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
              else 0)
        (∑ i ∈ Finset.range (m + 1),
          W i ω * (R (min (u i) (τ ω)) -
            R (min (u (i + 1)) (τ ω))))
    Integrable Z P → (∫ ω, Z ω ∂P) ≤ 0 := by
  let Z : Ω → ℝ := fun ω =>
    let u : ℕ → ℝ≥0 := fun i =>
      ((min i (m + 1) : ℕ) : ℝ≥0) * (T / (m + 1))
    let τ : Ω → ℝ≥0 := fun ξ =>
      (min (ruinTime X x D ξ) (T : ℝ≥0∞)).toNNReal
    let R : ℝ≥0 → ℝ := fun t =>
      ((t : ℝ) * X.drift - X.X t ω) -
        (∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
          else 0)
    (∑ i ∈ Finset.range (m + 1),
      W i ω * (R (min (u i) (τ ω)) -
        R (min (u (i + 1)) (τ ω))))
  change Integrable Z P → (∫ ω, Z ω ∂P) ≤ 0
  intro hInt
  have hResidual :=
    avram_p3_grid3_original_uniform_ruin_stopped_residual_nonpositive
      X hBV x D T m W hW
  have hNonpos : ∀ᵐ ω ∂P, Z ω ≤ 0 := by
    filter_upwards [hResidual] with ω hω
    exact hω
  exact integral_nonpos_of_ae hNonpos
