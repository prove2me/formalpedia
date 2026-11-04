-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_d_dividend_original_random_clock_ae_rightatom_absolute_cash_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T15:12:30.420254+00:00
-- url     : https://prove2.me/submissions/38bc735b-f10d-434c-8378-c66cefaba8f1

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_paymentTimes_all_rightjump_budget_no_preruin_premise
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Exact random-clock original signed and absolute right-dividend budget. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {ι : Type*}
    (X : SpectrallyNegativeLevy P 𝓕) (x q : ℝ) (hq : 0 ≤ q)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D) (w : ℝ → ℝ)
    (hjump : ∀ ω (s : ℝ≥0),
      (s = 0 ∨ (s : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D s ω - D s ω ≤ w (riskProcess X x D s ω) -
        w (riskProcess X x D s ω - (rightLimit D s ω - D s ω)))
    (t : Ω → ι → ℝ≥0) (τ : Ω → ℝ≥0)
    (hT : ∀ ω i, t ω i ≤ τ ω)
    (hPay : ∀ ω i, (t ω i : ℝ) ∈ paymentTimes (ruinTime X x D ω))
    (hInj : ∀ ω, Function.Injective (fun i : ι => (t ω i : ℝ)))
    (K : ℝ) (hK : 1 ≤ K)
    (hLocalSecant : ∀ ω i,
      w (riskProcess X x D (t ω i) ω) -
        w (x + X.X (t ω i) ω - rightLimit D (t ω i) ω) ≤
          K * (rightLimit D (t ω i) ω - D (t ω i) ω))
    (Cash : Ω → ℝ)
    (hCash : ∀ ω, Cash ω = (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal) :
    ∀ᵐ ω ∂P,
      let J : ι → ℝ := fun i => Real.exp (-(q * (t ω i : ℝ))) *
        ((rightLimit D (t ω i) ω - D (t ω i) ω) +
          w (x + X.X (t ω i) ω - rightLimit D (t ω i) ω) -
          w (riskProcess X x D (t ω i) ω))
      Summable J ∧ (∑' i : ι, J i) ≤ 0 ∧
        Summable (fun i : ι => |J i|) ∧
        (∑' i : ι, |J i|) ≤ (K - 1) * Cash ω := by
  apply Filter.Eventually.of_forall
  intro ω
  have hBound := avram_p4_d_dividend_original_paymentTimes_all_rightjump_budget_no_preruin_premise
    X x q hq D hD w hjump (t ω) ω (τ ω) (hT ω) (hPay ω) (hInj ω)
    K hK (hLocalSecant ω)
  simpa only [hCash ω] using hBound
