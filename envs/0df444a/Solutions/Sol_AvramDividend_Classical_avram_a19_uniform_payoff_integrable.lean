-- Prove2me | solution 1 for AvramDividend.Classical.avram_a19_uniform_payoff_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T12:14:26.719273+00:00
-- url     : https://prove2.me/submissions/82cf1d1a-dde6-4853-b185-e3794d5d1e5a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_a19_uniform_delta_profile
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_original_cash_prefix_positive_F_and_fatou

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The original bounded-variation physical-grid cash-plus-survival payoff is
    integrable at every uniform stopped-mesh index. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (q : ℝ) (hq : 0 ≤ q) (T : ℝ) (hT : 0 < T)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω)) :
    let δ : ℕ → ℝ := fun n => T / ((n : ℝ) + 2)
    let S : ℝ≥0 := ⟨T, le_of_lt hT⟩
    let F : ℕ → Ω → ℝ := fun n ω =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (T - δ n),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
      (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * T)) * w (riskProcess X x D S ω)
       else 0)
    ∀ n, Integrable (F n) P := by
  obtain ⟨hpos, hle, hanti, hlim⟩ :=
    avram_a19_uniform_delta_profile T hT
  have hcash :=
    avram_p3_grid4_original_cash_prefix_positive_F_and_fatou
      X hBV x C D hD w hw_cont hw_neg q hq T hT hw_nonneg
      (fun n => T / ((n : ℝ) + 2)) hpos hle hanti hlim
  exact fun n => (hcash.1 n).2.1
