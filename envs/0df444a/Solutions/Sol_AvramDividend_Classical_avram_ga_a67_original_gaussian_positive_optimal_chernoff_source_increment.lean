-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a67_original_gaussian_positive_optimal_chernoff_source_increment
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T07:38:19.37897+00:00
-- url     : https://prove2.me/submissions/1cf31dae-8b8e-439f-93dd-e99f106b5555

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a61_original_gaussian_positive_large_source_exp_tail_bound
import Theorems.Thm_AvramDividend_Classical_avram_ga_a62_positive_gaussian_chernoff_optimal_mesh_tilt
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Original pure Gaussian centred source positive exponential excursions have a sharp physical-mesh Chernoff exponent. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hν : X.ν = 0) (hσ : 0 < X.σ)
    (s t : ℝ≥0) (hst : s ≤ t)
    (hd : 0 < ((t - s : ℝ≥0) : ℝ))
    (θ δ : ℝ) (hθ : 0 ≤ θ)
    (hδ : θ * ((t - s : ℝ≥0) : ℝ) ≤ δ) :
    let Z : Ω → ℝ := fun ω =>
      ((X.X t ω - X.X s ω) -
        ((t - s : ℝ≥0) : ℝ) * X.c) / X.σ
    Integrable (fun ω => if δ ≤ Z ω then Real.exp (θ * Z ω) else 0) P →
    Integrable (fun ω => Real.exp
      ((θ + (δ / ((t - s : ℝ≥0) : ℝ) - θ)) * Z ω)) P →
    (∫ ω, if δ ≤ Z ω then Real.exp (θ * Z ω) else 0 ∂P) ≤
      Real.exp (θ * δ -
        δ^2 / (2 * ((t - s : ℝ≥0) : ℝ))) := by
  dsimp
  have hOpt := avram_ga_a62_positive_gaussian_chernoff_optimal_mesh_tilt
    ((t - s : ℝ≥0) : ℝ) θ δ hd hδ
  have h := avram_ga_a61_original_gaussian_positive_large_source_exp_tail_bound
    X hν hσ s t hst
    θ (δ / ((t - s : ℝ≥0) : ℝ) - θ) δ hθ hOpt.1
  intro hI hExpI
  have hB := h hI hExpI
  simpa only [hOpt.2] using hB
