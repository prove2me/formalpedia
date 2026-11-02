-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_08_original_perpetual_stieltjes_cash_integrable_q_ge_psi
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T00:15:43.404389+00:00
-- url     : https://prove2.me/submissions/0cec2ebb-40d2-44c1-84b0-0ef243bf8c8f

import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_08_original_perpetual_stieltjes_cash_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave6_08_original_perpetual_expected_cash_q_ge_psi
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : X.ψ 1 ≤ q) :
    Integrable (fun ω =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂dividendMeasure D ω).toReal) P := by
  let Cash : Ω → ℝ≥0∞ := fun ω =>
    ∫⁻ t in paymentTimes (ruinTime X x D ω),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂dividendMeasure D ω
  have hMeas : Measurable Cash :=
    avram_wave6_08_original_perpetual_stieltjes_cash_measurable X x D hD.1.1 q
  have hBound : (∫⁻ ω, Cash ω ∂P) ≤ ENNReal.ofReal (Real.exp x) :=
    avram_wave6_08_original_perpetual_expected_cash_q_ge_psi X x C D hD q hq
  have hFinite : ENNReal.ofReal (Real.exp x) < ⊤ := by simp
  have hCashFinite : (∫⁻ ω, Cash ω ∂P) ≠ ⊤ :=
    ne_of_lt (lt_of_le_of_lt hBound hFinite)
  exact integrable_toReal_of_lintegral_ne_top hMeas.aemeasurable hCashFinite
