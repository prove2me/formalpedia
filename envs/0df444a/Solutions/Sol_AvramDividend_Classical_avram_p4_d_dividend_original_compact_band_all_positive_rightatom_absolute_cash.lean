-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_d_dividend_original_compact_band_all_positive_rightatom_absolute_cash
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T20:07:27.283711+00:00
-- url     : https://prove2.me/submissions/37f07b5d-0502-498a-8e48-10e6ab55fb03

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_all_positive_preruin_rightatom_absolute_cash
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_rightpayment_local_lipschitz_secant_upper

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

/-- Actual stopped positive right-dividend atoms have an absolutely convergent
signed correction using only the source C1 bound on an honest reserve band. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x q : ℝ) (hq : 0 ≤ q)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D) (w : ℝ → ℝ)
    (hjump : ∀ ω (s : ℝ≥0),
      (s = 0 ∨ (s : ℝ≥0∞) < ruinTime X x D ω) →
        rightLimit D s ω - D s ω ≤ w (riskProcess X x D s ω) -
          w (riskProcess X x D s ω - (rightLimit D s ω - D s ω)))
    (ω : Ω) (T : ℝ≥0) (B : Set ℝ≥0)
    (hBExact : B = {t : ℝ≥0 | 0 < t ∧
      (t : ℝ≥0∞) < ruinTime X x D ω ∧ t ≤ T ∧
      0 < rightLimit D t ω - D t ω})
    (a b : ℝ) (L : ℝ≥0)
    (hDiff : ∀ y ∈ Icc a b, DifferentiableAt ℝ w y)
    (hDeriv : ∀ y ∈ Icc a b, ‖deriv w y‖₊ ≤ L)
    (hpre : ∀ t : B, riskProcess X x D (t : ℝ≥0) ω ∈ Icc a b)
    (hpost : ∀ t : B,
      x + X.X (t : ℝ≥0) ω - rightLimit D (t : ℝ≥0) ω ∈ Icc a b) :
    let J : B → ℝ := fun t => Real.exp (-(q * ((t : ℝ≥0) : ℝ))) *
      ((rightLimit D (t : ℝ≥0) ω - D (t : ℝ≥0) ω) +
        w (x + X.X (t : ℝ≥0) ω - rightLimit D (t : ℝ≥0) ω) -
        w (riskProcess X x D (t : ℝ≥0) ω))
    Summable J ∧ (∑' t : B, J t) ≤ 0 ∧
      Summable (fun t : B => |J t|) ∧
      (∑' t : B, |J t|) ≤ ((1 + (L : ℝ)) - 1) *
        (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal := by
  have hK : 1 ≤ (1 + (L : ℝ)) := by
    have hL : 0 ≤ (L : ℝ) := NNReal.coe_nonneg L
    linarith
  have hLocal : ∀ t : B,
      w (riskProcess X x D (t : ℝ≥0) ω) -
        w (x + X.X (t : ℝ≥0) ω - rightLimit D (t : ℝ≥0) ω) ≤
          (1 + (L : ℝ)) *
            (rightLimit D (t : ℝ≥0) ω - D (t : ℝ≥0) ω) := by
    intro t
    exact avram_p4_d_dividend_original_rightpayment_local_lipschitz_secant_upper
      X x D hD w a b L hDiff hDeriv ω (t : ℝ≥0) (hpre t) (hpost t)
  exact avram_p4_d_dividend_original_all_positive_preruin_rightatom_absolute_cash
    X x q hq D hD w hjump ω T B hBExact (1 + (L : ℝ)) hK hLocal
