-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_d_dividend_original_C2_event_masked_random_clock_atoms_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T16:13:22.554243+00:00
-- url     : https://prove2.me/submissions/d455d185-8dd2-43c5-8243-bc26d4038857

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_C2_event_local_rightatom_absolute_cash

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

/-- Real original right-atom L1 contribution after measurable C² interior localisation. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {ι : Type*} [Countable ι]
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
    (s : Set Ω) (hs : MeasurableSet s)
    (hPre : ∀ ω ∈ s, ∀ i, riskProcess X x D (t ω i) ω ∈ Icc a b)
    (hPost : ∀ ω ∈ s, ∀ i,
      x + X.X (t ω i) ω - rightLimit D (t ω i) ω ∈ Icc a b)
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
  change Integrable (s.indicator H) P ∧ (∀ᵐ ω ∂P, s.indicator H ω ≤ 0)
  have hMeas : AEStronglyMeasurable (s.indicator H) P :=
    (AEStronglyMeasurable.tsum hAtomTermMeas).indicator hs
  have hLocal : ∀ ω ∈ s,
      H ω ≤ 0 ∧ -H ω ≤ (max 1 (K : ℝ) - 1) * Cash ω := by
    intro ω hω
    have hAtom := avram_p4_d_dividend_original_C2_event_local_rightatom_absolute_cash
      X x q hq D hD w C hwC2 a b hOpen hBand K hK hjump
      t τ hT hPay hInj s hPre hPost Cash hCash ω hω
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
      _ ≤ (max 1 (K : ℝ) - 1) * Cash ω := hAbsBound
  have hSign : ∀ᵐ ω ∂P, s.indicator H ω ≤ 0 :=
    Filter.Eventually.of_forall (fun ω => by
      by_cases hω : ω ∈ s
      · rw [Set.indicator_of_mem hω]
        exact (hLocal ω hω).1
      · simpa only [Set.indicator_of_notMem hω] using (le_refl (0 : ℝ)))
  have hNorm : ∀ᵐ ω ∂P,
      ‖s.indicator H ω‖ ≤ ‖(max 1 (K : ℝ) - 1) * Cash ω‖ := by
    apply Filter.Eventually.of_forall
    intro ω
    by_cases hω : ω ∈ s
    · rw [Set.indicator_of_mem hω]
      have hCashNN : 0 ≤ Cash ω := by
        rw [hCash ω]
        exact ENNReal.toReal_nonneg
      have hEnvNN : 0 ≤ (max 1 (K : ℝ) - 1) * Cash ω :=
        mul_nonneg (sub_nonneg.mpr (le_max_left _ _)) hCashNN
      simpa only [Real.norm_eq_abs, abs_of_nonpos (hLocal ω hω).1,
        abs_of_nonneg hEnvNN] using (hLocal ω hω).2
    · simp only [Set.indicator_of_notMem hω, norm_zero]
      exact norm_nonneg _
  exact ⟨(hCashI.const_mul _).mono hMeas hNorm, hSign⟩
