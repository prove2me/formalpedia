-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a68_original_gaussian_normalised_increment_exp_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T07:38:13.036877+00:00
-- url     : https://prove2.me/submissions/e890b164-83e1-40e4-be14-abbe6e159107

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_zero_jump_original_compensated_increment_integrable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The original drift-centred zero-jump Gaussian physical increment, normalised by nonzero volatility, has a finite positive exponential moment. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (hσ : 0 < X.σ)
    (s t : ℝ≥0) (hst : s ≤ t)
    (θ : ℝ) (hθ : 0 ≤ θ) :
    Integrable (fun ω => Real.exp
      (θ * (((X.X t ω - X.X s ω) -
        ((t - s : ℝ≥0) : ℝ) * X.c) / X.σ))) P := by
  let β : ℝ := θ / X.σ
  have hβ : 0 ≤ β := div_nonneg hθ hσ.le
  have hI :=
    avram_p4_a_gaussian_zero_jump_original_compensated_increment_integrable
      X hν s t hst β hβ
  let a : ℝ := ((t - s : ℝ≥0) : ℝ) * (X.σ ^ 2 * β ^ 2 / 2)
  have hEq : (fun ω : Ω => Real.exp
      (θ * (((X.X t ω - X.X s ω) -
        ((t - s : ℝ≥0) : ℝ) * X.c) / X.σ))) =
      (fun ω : Ω => Real.exp a * Real.exp
        (β * ((X.X t ω - X.X s ω) -
          ((t - s : ℝ≥0) : ℝ) * X.c) - a)) := by
    funext ω
    rw [← Real.exp_add]
    congr 1
    dsimp [a, β]
    ring
  rw [hEq]
  exact hI.const_mul (Real.exp a)
