-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_B_original_physical_centered_source_expected_upper_by_bias
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T21:52:14.327079+00:00
-- url     : https://prove2.me/submissions/93833d3a-4dc3-4ffc-8d52-5a938be3ce36

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_jump6_B_original_physical_finite_grid_HJB_generator_Q_nonpositive
import Theorems.Thm_AvramDividend_Classical_avram_jump6_B_centred_source_signed_grid_bias_expected_bound
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section
set_option autoImplicit false

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (σ : Ω → ℝ≥0) (u : ℕ → ℕ → ℝ≥0) (m : ℕ → ℕ)
    (Source M Q : ℕ → Ω → ℝ) (bias : ℕ → ℝ)
    (hQphysical : ∀ j ω,
      Q j ω = (let v : ℕ → ℝ≥0 := fun i => min (u j i) (σ ω)
        let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
        let Y : ℝ≥0 → ℝ := fun t => x + X.X t ω - rightLimit D t ω
        ∑ i ∈ Finset.range (m j),
          E (v (i + 1)) * (((v (i + 1) - v i : ℝ≥0) : ℝ)) *
            (if 0 < Y (v i) ∧ ENNReal.ofReal (Y (v i)) < C then
              X.generator w (Y (v i)) - q * w (Y (v i))
             else 0)))
    (hM : ∀ j, Integrable (M j) P)
    (hQ : ∀ j, Integrable (Q j) P)
    (hMzero : ∀ j, (∫ ω, M j ω ∂P) = 0)
    (hSource : ∀ j ω, Source j ω = M j ω + Q j ω + bias j) :
    ∀ j, (∫ ω, Source j ω ∂P) ≤ bias j := by
  have hQmean : ∀ j, (∫ ω, Q j ω ∂P) ≤ 0 := by
    intro j
    apply MeasureTheory.integral_nonpos
    intro ω
    rw [hQphysical j ω]
    exact avram_jump6_B_original_physical_finite_grid_HJB_generator_Q_nonpositive
      X q w C hw_gen x D σ u m j ω
  exact avram_jump6_B_centred_source_signed_grid_bias_expected_bound
    P Source M Q bias hM hQ hMzero hQmean hSource