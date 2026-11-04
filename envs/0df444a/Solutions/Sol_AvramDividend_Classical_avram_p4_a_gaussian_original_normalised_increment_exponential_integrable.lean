-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_a_gaussian_original_normalised_increment_exponential_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T00:27:59.224864+00:00
-- url     : https://prove2.me/submissions/e838af22-11ab-4f95-89b6-35cb5a08f128

import Mathlib.Probability.IdentDistrib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_zero_jump_original_normalised_exponential_integrable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Original same-volatility Gaussian normalised increment exponentials are integrable. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X Y : SpectrallyNegativeLevy P 𝓕)
    (hν : Y.ν = 0) (hσeq : Y.σ = X.σ) (hσ : 0 < X.σ)
    (s t : ℝ≥0) (hst : s ≤ t) (θ : ℝ) (hθ : 0 ≤ θ) :
    Integrable (fun ω => Real.exp
      (θ * (((Y.X t ω - Y.X s ω) - ((t - s : ℝ≥0) : ℝ) * Y.c) / X.σ))) P := by
  have hMeas : Measurable (fun z : ℝ =>
      Real.exp (θ * ((z - ((t - s : ℝ≥0) : ℝ) * Y.c) / X.σ))) := by
    fun_prop
  have hLaw := (Y.stationaryIncrements s t hst).comp hMeas
  have hInt :=
    avram_p4_a_gaussian_zero_jump_original_normalised_exponential_integrable
      X Y hν hσeq hσ (t - s) θ hθ
  exact hLaw.integrable_iff.mpr hInt
