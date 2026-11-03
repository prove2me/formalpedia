-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_chat09_original_bv_bounded_random_clock_cash_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T09:58:34.550438+00:00
-- url     : https://prove2.me/submissions/a49b3500-f2ee-4014-bb20-2c65b4f7efe4

import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_chat09_original_bv_bounded_clock_closed_horizon_drift_budget
import Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_random_upper_clock_complete_stieltjes_cash_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (x : ℝ) (hx : 0 ≤ x) (C : ℝ≥0∞)
    (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 ≤ q)
    (T : ℝ≥0) (τ : Ω → ℝ≥0)
    (hτBound : ∀ ω, τ ω ≤ T)
    (hτMeas : Measurable (fun ω => ((τ ω : ℝ≥0) : ℝ))) :
    Integrable
      (fun ω => (∫⁻ t in
        paymentTimes (ruinTime X x D ω) ∩ Iic ((τ ω : ℝ≥0) : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal) P := by
  have hMeas : Measurable (fun ω : Ω =>
      ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic ((τ ω : ℝ≥0) : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) :=
    avram_wave6_06_original_random_upper_clock_complete_stieltjes_cash_measurable
      X x D hD.1.1 q (fun ω => ((τ ω : ℝ≥0) : ℝ)) hτMeas
  have hBound :=
    avram_wave6_chat09_original_bv_bounded_clock_closed_horizon_drift_budget
      X hX hBV x hx C hxc D hD q hq T τ hτBound
  have hFinite :
      (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
          Iic ((τ ω : ℝ≥0) : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) < ⊤ :=
    lt_of_le_of_lt hBound (by simp)
  exact integrable_toReal_of_lintegral_ne_top hMeas.aemeasurable (ne_of_lt hFinite)
