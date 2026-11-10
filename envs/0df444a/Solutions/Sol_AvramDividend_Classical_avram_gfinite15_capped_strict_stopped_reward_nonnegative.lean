-- Prove2me | solution 1 for AvramDividend.Classical.avram_gfinite15_capped_strict_stopped_reward_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T13:06:53.131208+00:00
-- url     : https://prove2.me/submissions/4ffda5e5-674b-4765-8275-9e33b832a3dd

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_finitecap_gradient_lower_bound_nonnegative_payoff

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hw0 : 0 ≤ w 0) (hwcont : ContinuousOn w (Ici 0))
    (hwDiff : DifferentiableOn ℝ w (Ioo 0 c))
    (hwGrad : ∀ y : ℝ, 0 < y → y < c → 1 ≤ deriv w y)
    (hwNeg : ∀ y < 0, w y = 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x (ENNReal.ofReal c) D)
    (q : ℝ) (σ : Ω → ℝ≥0) :
    ∀ ω, 0 < σ ω →
      0 ≤ Real.exp (-(q * (σ ω : ℝ))) *
        w (riskProcess X x D (σ ω) ω) +
        (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iio (σ ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure D ω)).toReal := by
  intro ω hpos
  have hcap : ENNReal.ofReal (riskProcess X x D (σ ω) ω) ≤
      ENNReal.ofReal c := hD.2 ω (σ ω) hpos
  have hwval : 0 ≤ w (riskProcess X x D (σ ω) ω) := by
    by_cases hneg : riskProcess X x D (σ ω) ω < 0
    · rw [hwNeg _ hneg]
    · have h0 : 0 ≤ riskProcess X x D (σ ω) ω := le_of_not_gt hneg
      have hle : riskProcess X x D (σ ω) ω ≤ c :=
        (ENNReal.ofReal_le_ofReal_iff hc).mp hcap
      exact avram_p4_e_localise_finitecap_gradient_lower_bound_nonnegative_payoff
        w c hc hw0 hwcont hwDiff hwGrad _ h0 hle
  exact add_nonneg (mul_nonneg (Real.exp_pos _).le hwval)
    ENNReal.toReal_nonneg
