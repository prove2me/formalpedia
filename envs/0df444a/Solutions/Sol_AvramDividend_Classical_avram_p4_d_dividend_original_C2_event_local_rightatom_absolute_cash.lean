-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_d_dividend_original_C2_event_local_rightatom_absolute_cash
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T15:57:33.14395+00:00
-- url     : https://prove2.me/submissions/3d093272-81b4-4439-994b-50f838ed4e9c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_random_clock_event_local_rightatom_cash_bound
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_C2_localband_actual_rightjump_secant_maxone

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- A source C² interior strip controls random right-payment atoms on its localisation event. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {ι : Type*}
    (X : SpectrallyNegativeLevy P 𝓕) (x q : ℝ) (hq : 0 ≤ q)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D) (w : ℝ → ℝ)
    (C : ℝ≥0∞)
    (hwC2 : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (a b : ℝ)
    (hOpen : IsOpen {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hBand : Icc a b ⊆ {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (K : ℝ≥0) (hK : ∀ y ∈ Icc a b, ‖deriv w y‖₊ ≤ K)
    (hjump : ∀ ω (r : ℝ≥0), (r = 0 ∨ (r : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D r ω - D r ω ≤ w (riskProcess X x D r ω) -
        w (riskProcess X x D r ω - (rightLimit D r ω - D r ω)))
    (t : Ω → ι → ℝ≥0) (τ : Ω → ℝ≥0)
    (hT : ∀ ω i, t ω i ≤ τ ω)
    (hPay : ∀ ω i, (t ω i : ℝ) ∈ paymentTimes (ruinTime X x D ω))
    (hInj : ∀ ω, Function.Injective (fun i : ι => (t ω i : ℝ)))
    (s : Set Ω)
    (hPre : ∀ ω ∈ s, ∀ i, riskProcess X x D (t ω i) ω ∈ Icc a b)
    (hPost : ∀ ω ∈ s, ∀ i,
      x + X.X (t ω i) ω - rightLimit D (t ω i) ω ∈ Icc a b)
    (Cash : Ω → ℝ)
    (hCash : ∀ ω, Cash ω = (∫⁻ u in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * u))) ∂(dividendMeasure D ω)).toReal) :
    ∀ ω ∈ s,
      let J : ι → ℝ := fun i => Real.exp (-(q * (t ω i : ℝ))) *
        ((rightLimit D (t ω i) ω - D (t ω i) ω) +
          w (x + X.X (t ω i) ω - rightLimit D (t ω i) ω) -
          w (riskProcess X x D (t ω i) ω))
      Summable J ∧ (∑' i : ι, J i) ≤ 0 ∧
        Summable (fun i : ι => |J i|) ∧
        (∑' i : ι, |J i|) ≤ (max 1 (K : ℝ) - 1) * Cash ω := by
  have hUpper : ∀ ω ∈ s, ∀ i,
      w (riskProcess X x D (t ω i) ω) -
        w (x + X.X (t ω i) ω - rightLimit D (t ω i) ω) ≤
          max 1 (K : ℝ) * (rightLimit D (t ω i) ω - D (t ω i) ω) := by
    intro ω hs i
    exact avram_p4_d_dividend_original_C2_localband_actual_rightjump_secant_maxone
      X x D hD C w hwC2 a b hOpen hBand K hK ω (t ω i)
      (hPre ω hs i) (hPost ω hs i)
  exact avram_p4_d_dividend_original_random_clock_event_local_rightatom_cash_bound
    X x q hq D hD w hjump t τ hT hPay hInj
    (max 1 (K : ℝ)) (le_max_left _ _) s hUpper Cash hCash
