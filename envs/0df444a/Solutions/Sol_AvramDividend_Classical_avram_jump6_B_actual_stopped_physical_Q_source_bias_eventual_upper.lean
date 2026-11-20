-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_B_actual_stopped_physical_Q_source_bias_eventual_upper
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T21:11:30.854851+00:00
-- url     : https://prove2.me/submissions/e5a1bcd4-0c29-48bb-aa87-e0a61dfbb11b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_jump6_B_original_physical_finite_grid_HJB_generator_Q_nonpositive
import Theorems.Thm_AvramDividend_Classical_avram_jump6_B_original_signed_mesh_vanishing_bias_eventual_upper
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section
set_option autoImplicit false

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (σ : Ω → ℝ≥0) (u : ℕ → ℕ → ℝ≥0) (m : ℕ → ℕ)
    (Source M : ℕ → Ω → ℝ) (bias : ℕ → ℝ)
    (hSource : ∀ j ω,
      let v : ℕ → ℝ≥0 := fun i => min (u j i) (σ ω)
      let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
      let Y : ℝ≥0 → ℝ := fun t => x + X.X t ω - rightLimit D t ω
      let Q : ℝ := ∑ i ∈ Finset.range (m j),
        E (v (i + 1)) * (((v (i + 1) - v i : ℝ≥0) : ℝ)) *
          (if 0 < Y (v i) ∧ ENNReal.ofReal (Y (v i)) < C then
            X.generator w (Y (v i)) - q * w (Y (v i))
           else 0)
      Source j ω = M j ω + Q + bias j)
    (hBias : Tendsto bias atTop (𝓝 (0 : ℝ))) :
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ j in atTop, ∀ ω, Source j ω ≤ M j ω + ε := by
  let Q : ℕ → Ω → ℝ := fun j ω =>
    let v : ℕ → ℝ≥0 := fun i => min (u j i) (σ ω)
    let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
    let Y : ℝ≥0 → ℝ := fun t => x + X.X t ω - rightLimit D t ω
    ∑ i ∈ Finset.range (m j),
      E (v (i + 1)) * (((v (i + 1) - v i : ℝ≥0) : ℝ)) *
        (if 0 < Y (v i) ∧ ENNReal.ofReal (Y (v i)) < C then
          X.generator w (Y (v i)) - q * w (Y (v i))
         else 0)
  have hQsign : ∀ j ω, Q j ω ≤ 0 := by
    intro j ω
    exact avram_jump6_B_original_physical_finite_grid_HJB_generator_Q_nonpositive
      X q w C hw_gen x D σ u m j ω
  have hSource' : ∀ j ω,
      Source j ω = M j ω + Q j ω + bias j := by
    intro j ω
    exact hSource j ω
  exact avram_jump6_B_original_signed_mesh_vanishing_bias_eventual_upper
    Source M Q bias hSource' hQsign hBias
