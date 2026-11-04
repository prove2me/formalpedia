-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_d_dividend_original_random_slope_event_masked_rightatom_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T16:08:47.157993+00:00
-- url     : https://prove2.me/submissions/3e1223a0-b2fd-4a2e-83f7-e283f4459fc8

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_paymentTimes_all_rightjump_budget_no_preruin_premise

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

/-- Event-local source right-atom remainder is L1 under a random integrable cash envelope. -/
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
    (s : Set Ω) (hs : MeasurableSet s)
    (K : Ω → ℝ) (hK : ∀ ω ∈ s, 1 ≤ K ω)
    (hLocalSecant : ∀ ω ∈ s, ∀ i,
      w (riskProcess X x D (t ω i) ω) -
        w (x + X.X (t ω i) ω - rightLimit D (t ω i) ω) ≤
          K ω * (rightLimit D (t ω i) ω - D (t ω i) ω))
    (Cash : Ω → ℝ)
    (hCash : ∀ ω, Cash ω = (∫⁻ u in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * u))) ∂(dividendMeasure D ω)).toReal)
    (hEnvelopeI : Integrable (s.indicator (fun ω => (K ω - 1) * Cash ω)) P)
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
  change Integrable (s.indicator H) P ∧ (∀ᵐ ω ∂P, s.indicator H ω ≤ 0)
  have hMeas : AEStronglyMeasurable (s.indicator H) P :=
    (AEStronglyMeasurable.tsum hAtomTermMeas).indicator hs
  have hCashNN : ∀ ω, 0 ≤ Cash ω := by
    intro ω
    rw [hCash ω]
    exact ENNReal.toReal_nonneg
  have hBoth : ∀ ω ∈ s, H ω ≤ 0 ∧ -H ω ≤ (K ω - 1) * Cash ω := by
    intro ω hω
    have hAtom := avram_p4_d_dividend_original_paymentTimes_all_rightjump_budget_no_preruin_premise
      X x q hq D hD w hjump (t ω) ω (τ ω)
      (hT ω) (hPay ω) (hInj ω) (K ω) (hK ω hω) (hLocalSecant ω hω)
    dsimp only at hAtom
    rcases hAtom with ⟨hSum, hNonpos, hAbsSum, hAbsBound⟩
    let J : ι → ℝ := fun i => Real.exp (-(q * (t ω i : ℝ))) *
      ((rightLimit D (t ω i) ω - D (t ω i) ω) +
        w (x + X.X (t ω i) ω - rightLimit D (t ω i) ω) -
        w (riskProcess X x D (t ω i) ω))
    have hDom : -(∑' i, J i) ≤ ∑' i, |J i| := by
      calc
        -(∑' i, J i) = ∑' i, -J i := (tsum_neg).symm
        _ ≤ ∑' i, |J i| :=
          hSum.neg.tsum_le_tsum (fun i => neg_le_abs (J i)) hAbsSum
    refine ⟨hNonpos, ?_⟩
    calc
      -H ω = -(∑' i, J i) := rfl
      _ ≤ ∑' i, |J i| := hDom
      _ ≤ (K ω - 1) * Cash ω := by simpa only [hCash ω] using hAbsBound
  have hSign : ∀ᵐ ω ∂P, s.indicator H ω ≤ 0 :=
    Filter.Eventually.of_forall (fun ω => by
      by_cases hω : ω ∈ s
      · rw [Set.indicator_of_mem hω]
        exact (hBoth ω hω).1
      · simpa only [Set.indicator_of_notMem hω] using (le_refl (0 : ℝ)))
  have hNorm : ∀ᵐ ω ∂P,
      ‖s.indicator H ω‖ ≤ ‖s.indicator (fun ω => (K ω - 1) * Cash ω) ω‖ := by
    apply Filter.Eventually.of_forall
    intro ω
    by_cases hω : ω ∈ s
    · rw [Set.indicator_of_mem hω, Set.indicator_of_mem hω]
      have hEnvNN : 0 ≤ (K ω - 1) * Cash ω :=
        mul_nonneg (sub_nonneg.mpr (hK ω hω)) (hCashNN ω)
      simpa only [Real.norm_eq_abs, abs_of_nonpos (hBoth ω hω).1,
        abs_of_nonneg hEnvNN] using (hBoth ω hω).2
    · simp only [Set.indicator_of_notMem hω, norm_zero, le_refl]
  exact ⟨hEnvelopeI.mono hMeas hNorm, hSign⟩
