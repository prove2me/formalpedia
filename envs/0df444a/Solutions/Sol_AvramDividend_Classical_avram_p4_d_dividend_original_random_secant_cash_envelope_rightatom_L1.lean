-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_d_dividend_original_random_secant_cash_envelope_rightatom_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T16:08:51.153458+00:00
-- url     : https://prove2.me/submissions/f9980418-2b30-4c7e-a66e-c8d3fd024c31

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

/-- A random integrable secant-cash envelope bounds the actual original right-atom remainder. -/
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
    (K : Ω → ℝ) (hK : ∀ ω, 1 ≤ K ω)
    (hLocalSecant : ∀ ω i,
      w (riskProcess X x D (t ω i) ω) -
        w (x + X.X (t ω i) ω - rightLimit D (t ω i) ω) ≤
          K ω * (rightLimit D (t ω i) ω - D (t ω i) ω))
    (Cash : Ω → ℝ)
    (hCash : ∀ ω, Cash ω = (∫⁻ u in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * u))) ∂(dividendMeasure D ω)).toReal)
    (hEnvelopeI : Integrable (fun ω => (K ω - 1) * Cash ω) P)
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
    Integrable H P ∧ (∀ᵐ ω ∂P, H ω ≤ 0) := by
  let H : Ω → ℝ := fun ω => ∑' i : ι,
    Real.exp (-(q * (t ω i : ℝ))) *
      ((rightLimit D (t ω i) ω - D (t ω i) ω) +
        w (x + X.X (t ω i) ω - rightLimit D (t ω i) ω) -
        w (riskProcess X x D (t ω i) ω))
  change Integrable H P ∧ (∀ᵐ ω ∂P, H ω ≤ 0)
  have hMeas : AEStronglyMeasurable H P :=
    AEStronglyMeasurable.tsum hAtomTermMeas
  have hCashNN : ∀ ω, 0 ≤ Cash ω := by
    intro ω
    rw [hCash ω]
    exact ENNReal.toReal_nonneg
  have hBoth : ∀ ω, H ω ≤ 0 ∧ -H ω ≤ (K ω - 1) * Cash ω := by
    intro ω
    have hAtom := avram_p4_d_dividend_original_paymentTimes_all_rightjump_budget_no_preruin_premise
      X x q hq D hD w hjump (t ω) ω (τ ω)
      (hT ω) (hPay ω) (hInj ω) (K ω) (hK ω) (hLocalSecant ω)
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
  have hSign : ∀ᵐ ω ∂P, H ω ≤ 0 := Filter.Eventually.of_forall (fun ω => (hBoth ω).1)
  have hNorm : ∀ᵐ ω ∂P, ‖H ω‖ ≤ ‖(K ω - 1) * Cash ω‖ := by
    apply Filter.Eventually.of_forall
    intro ω
    have hEnvNN : 0 ≤ (K ω - 1) * Cash ω :=
      mul_nonneg (sub_nonneg.mpr (hK ω)) (hCashNN ω)
    simpa only [Real.norm_eq_abs, abs_of_nonpos (hBoth ω).1,
      abs_of_nonneg hEnvNN] using (hBoth ω).2
  exact ⟨hEnvelopeI.mono hMeas hNorm, hSign⟩
