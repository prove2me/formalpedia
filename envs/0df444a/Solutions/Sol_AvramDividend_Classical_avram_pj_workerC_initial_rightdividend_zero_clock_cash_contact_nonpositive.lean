-- Prove2me | solution 1 for AvramDividend.Classical.avram_pj_workerC_initial_rightdividend_zero_clock_cash_contact_nonpositive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T08:10:30.776362+00:00
-- url     : https://prove2.me/submissions/661223de-e1a9-450c-b5a7-9af54741f399

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_zero_clock_real_cash_eq_initial_rightatom
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_le_rightLimit
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
    (x q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
        w (riskProcess X x D t ω -
          (rightLimit D t ω - D t ω)))
    (τ : Ω → ℝ≥0) (Cash : Ω → ℝ)
    (hCash : ∀ ω, Cash ω =
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure D ω)).toReal)
    (ω : Ω) (hZero : τ ω = 0) :
    Cash ω +
      w (riskProcess X x D 0 ω -
        (rightLimit D 0 ω - D 0 ω)) ≤
      w (riskProcess X x D 0 ω) := by
  have hStrat : IsDividendStrategy 𝓕 D := hD.1.1
  have hPay : 0 ≤ rightLimit D 0 ω - D 0 ω := by
    exact sub_nonneg.mpr
      (AvramDividend.Classical.dividendStrategy_le_rightLimit D hStrat ω 0)
  have hCash0 :=
    AvramDividend.Classical.avram_p4_d_dividend_original_zero_clock_real_cash_eq_initial_rightatom
      X x q D hStrat τ Cash hCash ω hZero
  have hCashEq : Cash ω = rightLimit D 0 ω - D 0 ω := by
    simpa [ENNReal.toReal_ofReal hPay] using hCash0
  rw [hCashEq]
  have hJump := hjump ω 0 (Or.inl rfl)
  linarith

