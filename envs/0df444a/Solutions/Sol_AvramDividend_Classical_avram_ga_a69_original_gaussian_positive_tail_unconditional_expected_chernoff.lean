-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a69_original_gaussian_positive_tail_unconditional_expected_chernoff
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T07:57:03.828019+00:00
-- url     : https://prove2.me/submissions/dcbd8cf9-945f-4752-8207-faa079b10a9a

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a61_original_gaussian_positive_large_source_exp_tail_bound
import Theorems.Thm_AvramDividend_Classical_avram_ga_a68_original_gaussian_normalised_increment_exp_integrable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Original Gaussian source positive exponential tail requires no extra integrability beyond the source process. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hν : X.ν = 0) (hσ : 0 < X.σ)
    (s t : ℝ≥0) (hst : s ≤ t)
    (Z : Ω → ℝ)
    (hZ : Z = (fun ω => ((X.X t ω - X.X s ω) -
      ((t - s : ℝ≥0) : ℝ) * X.c) / X.σ))
    (hMeas : Measurable Z)
    (θ r δ : ℝ) (hθ : 0 ≤ θ) (hr : 0 ≤ r) :
    (∫ ω, if δ ≤ Z ω then Real.exp (θ * Z ω) else 0 ∂P) ≤
      Real.exp (-r * δ + ((t - s : ℝ≥0) : ℝ) * (θ + r)^2 / 2) := by
  have hθr : 0 ≤ θ + r := add_nonneg hθ hr
  have hExpI : Integrable (fun ω => Real.exp ((θ + r) * Z ω)) P := by
    rw [hZ]
    exact avram_ga_a68_original_gaussian_normalised_increment_exp_integrable
      X hν hσ s t hst (θ + r) hθr
  have hExpBase : Integrable (fun ω => Real.exp (θ * Z ω)) P := by
    rw [hZ]
    exact avram_ga_a68_original_gaussian_normalised_increment_exp_integrable
      X hν hσ s t hst θ hθ
  have hEvent : MeasurableSet {ω : Ω | δ ≤ Z ω} :=
    measurableSet_le measurable_const hMeas
  have hTailI : Integrable (fun ω => if δ ≤ Z ω then
      Real.exp (θ * Z ω) else 0) P :=
    hExpBase.indicator hEvent
  subst Z
  exact avram_ga_a61_original_gaussian_positive_large_source_exp_tail_bound
    X hν hσ s t hst θ r δ hθ hr hTailI hExpI
