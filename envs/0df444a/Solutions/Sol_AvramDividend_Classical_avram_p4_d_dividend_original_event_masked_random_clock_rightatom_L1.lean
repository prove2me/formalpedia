-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_d_dividend_original_event_masked_random_clock_rightatom_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T16:10:52.964126+00:00
-- url     : https://prove2.me/submissions/209ea2ec-517d-4129-97d5-fdfd09887fe0

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_random_clock_event_local_rightatom_cash_bound
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_full_stieltjes_cash_dominates_integrable_negative_residual

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

/-- The original dividend right-atom residual localized to a measurable path event is L1. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {ι : Type*} [Countable ι]
    (X : SpectrallyNegativeLevy P 𝓕) (x q : ℝ) (hq : 0 ≤ q)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D) (w : ℝ → ℝ)
    (hjump : ∀ ω (r : ℝ≥0), (r = 0 ∨ (r : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D r ω - D r ω ≤ w (riskProcess X x D r ω) -
        w (riskProcess X x D r ω - (rightLimit D r ω - D r ω)))
    (t : Ω → ι → ℝ≥0) (τ : Ω → ℝ≥0)
    (hT : ∀ ω i, t ω i ≤ τ ω)
    (hPay : ∀ ω i, (t ω i : ℝ) ∈ paymentTimes (ruinTime X x D ω))
    (hInj : ∀ ω, Function.Injective (fun i : ι => (t ω i : ℝ)))
    (K : ℝ) (hK : 1 ≤ K) (s : Set Ω) (hs : MeasurableSet s)
    (hLocalSecant : ∀ ω ∈ s, ∀ i,
      w (riskProcess X x D (t ω i) ω) -
        w (x + X.X (t ω i) ω - rightLimit D (t ω i) ω) ≤
          K * (rightLimit D (t ω i) ω - D (t ω i) ω))
    (Cash : Ω → ℝ)
    (hCash : ∀ ω, Cash ω = (∫⁻ u in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * u))) ∂(dividendMeasure D ω)).toReal)
    (hCashI : Integrable Cash P)
    (hAtomTermMeas : ∀ i : ι,
      AEStronglyMeasurable (fun ω => Real.exp (-(q * (t ω i : ℝ))) *
        ((rightLimit D (t ω i) ω - D (t ω i) ω) +
          w (x + X.X (t ω i) ω - rightLimit D (t ω i) ω) -
          w (riskProcess X x D (t ω i) ω))) P) :
    let H : Ω → ℝ := fun ω => ∑' i : ι,
      Real.exp (-(q * (t ω i : ℝ))) *
        ((rightLimit D (t ω i) ω - D (t ω i) ω) +
          w (x + X.X (t ω i) ω - rightLimit D (t ω i) ω) -
          w (riskProcess X x D (t ω i) ω))
    Integrable (s.indicator H) P ∧
      (∀ᵐ ω ∂P, s.indicator H ω ≤ 0) := by
  let H : Ω → ℝ := fun ω => ∑' i : ι,
    Real.exp (-(q * (t ω i : ℝ))) *
      ((rightLimit D (t ω i) ω - D (t ω i) ω) +
        w (x + X.X (t ω i) ω - rightLimit D (t ω i) ω) -
        w (riskProcess X x D (t ω i) ω))
  change Integrable (s.indicator H) P ∧
    (∀ᵐ ω ∂P, s.indicator H ω ≤ 0)
  have hBound := avram_p4_d_dividend_original_random_clock_event_local_rightatom_cash_bound
    X x q hq D hD w hjump t τ hT hPay hInj K hK s hLocalSecant Cash hCash
  have hMeas : AEStronglyMeasurable (s.indicator H) P :=
    (AEStronglyMeasurable.tsum hAtomTermMeas).indicator hs
  have hCashNN : ∀ ω, 0 ≤ Cash ω := by
    intro ω
    rw [hCash ω]
    exact ENNReal.toReal_nonneg
  have hSign : ∀ᵐ ω ∂P, s.indicator H ω ≤ 0 :=
    Filter.Eventually.of_forall (fun ω => by
      by_cases hω : ω ∈ s
      · rw [Set.indicator_of_mem hω]
        exact (hBound ω hω).2.1
      · simpa only [Set.indicator_of_notMem hω] using (le_refl (0 : ℝ)))
  have hUpper : ∀ᵐ ω ∂P, -(s.indicator H ω) ≤ (K - 1) * Cash ω :=
    Filter.Eventually.of_forall (fun ω => by
      by_cases hω : ω ∈ s
      · rw [Set.indicator_of_mem hω]
        let J : ι → ℝ := fun i => Real.exp (-(q * (t ω i : ℝ))) *
          ((rightLimit D (t ω i) ω - D (t ω i) ω) +
            w (x + X.X (t ω i) ω - rightLimit D (t ω i) ω) -
            w (riskProcess X x D (t ω i) ω))
        have hωBound := hBound ω hω
        dsimp only at hωBound
        rcases hωBound with ⟨hSum, hNonpos, hAbsSum, hAbsBound⟩
        have hDom : -(∑' i, J i) ≤ ∑' i, |J i| := by
          calc
            -(∑' i, J i) = ∑' i, -J i := (tsum_neg).symm
            _ ≤ ∑' i, |J i| :=
              hSum.neg.tsum_le_tsum (fun i => neg_le_abs (J i)) hAbsSum
        calc
          -H ω = -(∑' i, J i) := rfl
          _ ≤ ∑' i, |J i| := hDom
          _ ≤ (K - 1) * Cash ω := hAbsBound
      · rw [Set.indicator_of_notMem hω]
        simpa using mul_nonneg (sub_nonneg.mpr hK) (hCashNN ω))
  exact avram_p4_d_dividend_original_full_stieltjes_cash_dominates_integrable_negative_residual
    X x q hq D hD τ Cash (s.indicator H) hCash hCashI hMeas K hK hSign hUpper
