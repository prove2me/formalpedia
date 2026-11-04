-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_d_dividend_original_random_clock_signed_rightatom_L1_of_measurable_sum
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T15:39:59.586825+00:00
-- url     : https://prove2.me/submissions/e755fdf2-f618-46e1-a127-9fb72a0567f7

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_random_clock_ae_rightatom_absolute_cash_bound
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_full_stieltjes_cash_dominates_integrable_negative_residual

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

/-- Exact random-clock source-ordered right-dividend sum is integrable when measurable. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {ι : Type*}
    (X : SpectrallyNegativeLevy P 𝓕) (x q : ℝ) (hq : 0 ≤ q)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D) (w : ℝ → ℝ)
    (hjump : ∀ ω (s : ℝ≥0), (s = 0 ∨ (s : ℝ≥0∞) < ruinTime X x D ω) →
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
    (Cash Hatom : Ω → ℝ)
    (hCash : ∀ ω, Cash ω = (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal)
    (hCashI : Integrable Cash P)
    (hHatom : ∀ ω, Hatom ω = ∑' i : ι,
      Real.exp (-(q * (t ω i : ℝ))) *
        ((rightLimit D (t ω i) ω - D (t ω i) ω) +
          w (x + X.X (t ω i) ω - rightLimit D (t ω i) ω) -
          w (riskProcess X x D (t ω i) ω)))
    (hHatomMeas : AEStronglyMeasurable Hatom P) :
    Integrable Hatom P ∧ (∀ᵐ ω ∂P, Hatom ω ≤ 0) := by
  have hAtom :=
    avram_p4_d_dividend_original_random_clock_ae_rightatom_absolute_cash_bound
      X x q hq D hD w hjump t τ hT hPay hInj K hK hLocalSecant Cash hCash
  have hSign : ∀ᵐ ω ∂P, Hatom ω ≤ 0 := by
    filter_upwards [hAtom] with ω hω
    dsimp only at hω
    rw [hHatom ω]
    exact hω.2.1
  have hBound : ∀ᵐ ω ∂P, -Hatom ω ≤ (K - 1) * Cash ω := by
    filter_upwards [hAtom] with ω hω
    dsimp only at hω
    let J : ι → ℝ := fun i => Real.exp (-(q * (t ω i : ℝ))) *
      ((rightLimit D (t ω i) ω - D (t ω i) ω) +
        w (x + X.X (t ω i) ω - rightLimit D (t ω i) ω) -
        w (riskProcess X x D (t ω i) ω))
    have hDom : -(∑' i, J i) ≤ ∑' i, |J i| := by
      calc
        -(∑' i, J i) = ∑' i, -J i := (tsum_neg).symm
        _ ≤ ∑' i, |J i| :=
          hω.1.neg.tsum_le_tsum (fun i => neg_le_abs (J i)) hω.2.2.1
    calc
      -Hatom ω = -(∑' i, J i) := by rw [hHatom ω]
      _ ≤ ∑' i, |J i| := hDom
      _ ≤ (K - 1) * Cash ω := hω.2.2.2
  exact avram_p4_d_dividend_original_full_stieltjes_cash_dominates_integrable_negative_residual
    X x q hq D hD τ Cash Hatom hCash hCashI hHatomMeas K hK hSign hBound
