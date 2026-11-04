-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_a_gaussian_zero_jump_original_normalised_exponential_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T23:40:42.175064+00:00
-- url     : https://prove2.me/submissions/98091099-2e34-4eb1-ac15-0074a78f606c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_zero_jump_original_centered_exponential_integrable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Positive exponential moments of the same-source normalised zero-jump
component are integrable. This supplies the finite-mgf premise for
Gaussian law identification without assuming the existence of Brownian motion. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X Y : SpectrallyNegativeLevy P 𝓕)
    (hν : Y.ν = 0) (hσeq : Y.σ = X.σ) (hσ : 0 < X.σ)
    (t : ℝ≥0) (θ : ℝ) (hθ : 0 ≤ θ) :
    Integrable (fun ω => Real.exp
      (θ * ((Y.X t ω - (t : ℝ) * Y.c) / X.σ))) P := by
  have hscaled : 0 ≤ θ / X.σ := div_nonneg hθ (le_of_lt hσ)
  have hInt :=
    avram_p4_a_gaussian_zero_jump_original_centered_exponential_integrable
      Y hν t (θ / X.σ) hscaled
  have heq :
      (fun ω => Real.exp
        (θ * ((Y.X t ω - (t : ℝ) * Y.c) / X.σ))) =
      (fun ω => Real.exp
        ((θ / X.σ) * (Y.X t ω - (t : ℝ) * Y.c))) := by
    funext ω
    congr 1
    ring
  rw [heq]
  exact hInt
