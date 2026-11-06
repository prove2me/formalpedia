-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_hor3_original_positive_ruin_weighted_budget_glues_closed_horizon
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T18:09:22.762095+00:00
-- url     : https://prove2.me/submissions/bc4b8676-1cfd-4d04-825f-524e564c387d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_hor3_original_ito_boundary_union_pointwise_cash_le
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x q : ℝ)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))
    (n : ℕ) (hn : 0 < n) (T : ℝ) (hT : 0 < T)
    (Cash : Ω → ℝ≥0∞)
    (hCash : ∀ ω, Cash ω =
      (∫⁻ t in paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)))
    (hEvent : MeasurableSet {ω : Ω | ruinTime X x D ω = 0})
    (hInterior :
      (∫⁻ ω in {ω : Ω | ruinTime X x D ω ≠ 0}, Cash ω ∂P) ≤
        ENNReal.ofReal (w x) * P {ω : Ω | ruinTime X x D ω ≠ 0}) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
      ENNReal.ofReal (w x) := by
  let A : Set Ω := {ω | ruinTime X x D ω = 0}
  let budget : ℝ≥0∞ := ENNReal.ofReal (w x)
  letI : IsProbabilityMeasure P := X.isProbability
  have hPoint : ∀ ω ∈ A, Cash ω ≤ budget := by
    intro ω hω
    rw [hCash ω]
    exact avram_ubv_hor3_original_ito_boundary_union_pointwise_cash_le
      X x q w C hw0 hw_cont hw_neg hw_smooth hw_grad hxc
      D hD hjump n T (le_of_lt hT) ω (Or.inr (Or.inr hω))
  have hMask :
      (∫⁻ ω, A.indicator Cash ω ∂P) ≤
        (∫⁻ ω, A.indicator (fun _ => budget) ω ∂P) := by
    apply lintegral_mono
    intro ω
    by_cases hω : ω ∈ A
    · simpa [hω] using hPoint ω hω
    · simp [hω]
  have hBoundary :
      (∫⁻ ω in A, Cash ω ∂P) ≤ budget * P A := by
    calc
      (∫⁻ ω in A, Cash ω ∂P) =
        (∫⁻ ω, A.indicator Cash ω ∂P) :=
          (lintegral_indicator hEvent Cash).symm
      _ ≤ (∫⁻ ω, A.indicator (fun _ => budget) ω ∂P) := hMask
      _ = (∫⁻ ω in A, budget ∂P) :=
        lintegral_indicator hEvent (fun _ => budget)
      _ = budget * P A := by simp [lintegral_const, mul_comm]
  have hMass : P A + P Aᶜ = 1 := by
    calc
      P A + P Aᶜ = P Set.univ := measure_add_measure_compl hEvent
      _ = 1 := measure_univ
  have hSplit :
      (∫⁻ ω, Cash ω ∂P) =
        (∫⁻ ω in A, Cash ω ∂P) +
        (∫⁻ ω in Aᶜ, Cash ω ∂P) := by
    calc
      (∫⁻ ω, Cash ω ∂P) =
        (∫⁻ ω, Cash ω ∂(P.restrict A + P.restrict Aᶜ)) := by
          rw [Measure.restrict_add_restrict_compl hEvent]
      _ = _ := lintegral_add_measure Cash (P.restrict A) (P.restrict Aᶜ)
  have hInterior' :
      (∫⁻ ω in Aᶜ, Cash ω ∂P) ≤ budget * P Aᶜ := hInterior
  have hFull : (∫⁻ ω, Cash ω ∂P) ≤ budget := by
    calc
      _ = (∫⁻ ω in A, Cash ω ∂P) +
          (∫⁻ ω in Aᶜ, Cash ω ∂P) := hSplit
      _ ≤ budget * P A + budget * P Aᶜ := add_le_add hBoundary hInterior'
      _ = budget := by rw [← mul_add, hMass, mul_one]
  simpa only [hCash] using hFull
