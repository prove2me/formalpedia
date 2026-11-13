-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a40_original_gaussian_fixed_horizon_exponential_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T12:59:32.964709+00:00
-- url     : https://prove2.me/submissions/9e4e69b1-231f-436f-8ea7-07a60115a27e

import Mathlib.Probability.Distributions.Exponential
import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_avram_ga_a37_gaussian_positive_rate_above_growth
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_expMeasure_strict_survival_positive
import Theorems.Thm_AvramDividend_Classical_avram_ga_a38_original_fixed_horizon_supremum_exponential_lintegral
import Theorems.Thm_AvramDividend_Classical_avram_ga_a39_original_exponential_clock_supremum_integrable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hSigma : 0 < X.σ)
    (n : ℝ≥0) (beta : ℝ) (hbeta : 0 ≤ beta) :
    (∫⁻ ω : Ω,
      ENNReal.ofReal (Real.exp (beta * runningSup X n ω))
        ∂ P) < ⊤ := by
  letI : IsProbabilityMeasure P := X.isProbability
  rcases avram_ga_a37_gaussian_positive_rate_above_growth
      X hSigma beta hbeta with ⟨ p, lam, hp, hlam, hbetaLam, hroot ⟩
  letI : IsProbabilityMeasure (expMeasure p) :=
    isProbabilityMeasure_expMeasure hp
  have hMoment :=
    avram_ga_a39_original_exponential_clock_supremum_integrable
      X p lam beta hp hlam hroot hbetaLam
  have hTail : 0 < expMeasure p (Set.Ioi (n : ℝ)) :=
    avram_ws01e_b_expMeasure_strict_survival_positive
      p (n : ℝ) hp n.property
  exact avram_ga_a38_original_fixed_horizon_supremum_exponential_lintegral
    X (expMeasure p) n beta hbeta hTail hMoment
