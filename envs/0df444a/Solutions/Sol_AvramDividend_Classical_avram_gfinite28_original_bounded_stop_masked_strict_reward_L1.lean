-- Prove2me | solution 1 for AvramDividend.Classical.avram_gfinite28_original_bounded_stop_masked_strict_reward_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T03:45:00.739939+00:00
-- url     : https://prove2.me/submissions/08ef0f0b-9941-46cd-a922-91940919ea0a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_finite13_original_stopped_prepayment_terminal_L1
import Theorems.Thm_AvramDividend_Classical_avram_ubv_gauss13_endpoint_original_bounded_stopped_strict_cash_L1
import Theorems.Thm_AvramDividend_Classical_avram_ubv_loc6_rightcont_stopping_zero_mask_integrable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Original finite-cap stopped strict reward is integrable, with its true zero-clock value. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (hfinite : C ≠ ⊤)
    (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (q : ℝ) (hq : 0 < q) (σ : Ω → ℝ≥0)
    (hσstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (σ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hσbound : ∀ ω, σ ω ≤ T) :
    Integrable (fun ω =>
      if σ ω = 0 then w x else
        Real.exp (-(q * (σ ω : ℝ))) *
          w (riskProcess X x D (σ ω) ω) +
        (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iio (σ ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure D ω)).toReal) P := by
  letI : IsProbabilityMeasure P := X.isProbability
  have hTerm : Integrable (fun ω =>
      Real.exp (-(q * (σ ω : ℝ))) *
        w (riskProcess X x D (σ ω) ω)) P :=
    avram_ubv_finite13_original_stopped_prepayment_terminal_L1
      X x C hfinite hxc D hD w hw_cont hw_neg q (le_of_lt hq) σ hσstop
  have hCash : Integrable (fun ω =>
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iio (σ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal) P :=
    avram_ubv_gauss13_endpoint_original_bounded_stopped_strict_cash_L1
      X x C D hD q (le_of_lt hq) σ hσstop T hσbound
  exact avram_ubv_loc6_rightcont_stopping_zero_mask_integrable
    σ hσstop _ (hTerm.add hCash) (w x)
