-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f4_mixed_gaussian_jump_allcap_positive_clock_weighted_budget
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T06:49:54.641475+00:00
-- url     : https://prove2.me/submissions/c5231400-a024-4a8a-8f88-4347b25f5e82
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Probability.Process.Stopping
import Theorems.Thm_AvramDividend_Classical_avram_p4_f4_original_positive_clock_zero_vanishing_stochastic_envelope
import Theorems.Thm_AvramDividend_Classical_avram_p4_f4_positive_clock_real_budget_from_zero_vanishing_center
import Theorems.Thm_AvramDividend_Classical_avram_p4_f4_positive_clock_real_to_ennreal_weighted_budget
import Theorems.Thm_AvramDividend_Classical_avram_p4_f4_original_natural_clock_three_signs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν ≠ 0) (hσ : X.σ ≠ 0) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 < x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω))
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (n : ℕ) (hn : 0 < n) (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω = (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (hτmeas : Measurable (fun ω => (τ ω : ℝ)))
    (hτstop : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
    (W Cash Term : Ω → ℝ)
    (hW : ∀ ω, W ω = if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω
      then x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω)
    (hCash : ∀ ω, Cash ω = (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal)
    (hTerm : ∀ ω, Term ω = Real.exp (-(q * (τ ω : ℝ))) * w (W ω))
    (hTermMeas : AEStronglyMeasurable Term P)
    (hCashI : Integrable Cash P) :
    (∫⁻ ω in {ω | τ ω ≠ 0}, ENNReal.ofReal (Term ω + Cash ω) ∂P) ≤
      ENNReal.ofReal (w x) * P {ω | τ ω ≠ 0} := by
  letI : IsProbabilityMeasure P := X.isProbability
  obtain ⟨M, hTermI, hMI, hMzero, hVan, hUpper⟩ :=
    AvramDividend.Classical.avram_p4_f4_original_positive_clock_zero_vanishing_stochastic_envelope
      X hX hBV hν hσ q hq w C hC hw0 hw_cont hw_neg hw_smooth
      hw_gen hw_grad x hx hxc D hD hw_nonneg hjump n hn τ hτeq
      hτmeas hτstop W Cash Term hW hCash hTerm hTermMeas hCashI
  obtain ⟨hwx, hTermPos, hCashPos⟩ :=
    AvramDividend.Classical.avram_p4_f4_original_natural_clock_three_signs
      X hX hBV q hq w C hC hw0 hw_cont hw_neg hw_smooth
      hw_gen hw_grad x hx hxc D hD hw_nonneg hjump n hn τ hτeq
      hτmeas hτstop W Cash Term hW hCash hTerm hTermMeas hCashI
  let S : Set Ω := {ω | τ ω ≠ 0}
  have hS : MeasurableSet S := by
    have hzero : MeasurableSet {ω | (τ ω : ℝ) = 0} :=
      measurableSet_eq_fun hτmeas measurable_const
    have hSet : S = {ω | (τ ω : ℝ) = 0}ᶜ := by
      ext ω
      simp [S]
    rw [hSet]
    exact hzero.compl
  have hZeroOutside : ∀ᵐ ω ∂P, ω ∉ S → M ω = 0 := by
    filter_upwards [hVan] with ω hv hout
    apply hv
    simpa [S] using hout
  have hSumI : Integrable (fun ω => Term ω + Cash ω) P := hTermI.add hCashI
  have hRealBudget :
      (∫ ω in S, Term ω + Cash ω ∂P) ≤ (∫ ω in S, w x ∂P) :=
    AvramDividend.Classical.avram_p4_f4_positive_clock_real_budget_from_zero_vanishing_center
      S hS (fun ω => Term ω + Cash ω) M (w x)
      hSumI hMI hMzero hZeroOutside hUpper
  have hMeanS :
      (∫ ω in S, Term ω + Cash ω ∂P) ≤ w x * (P S).toReal := by
    calc
      (∫ ω in S, Term ω + Cash ω ∂P) ≤
          (∫ ω in S, w x ∂P) := hRealBudget
      _ = w x * (P S).toReal := by simp [setIntegral_const, Measure.real, mul_comm]
  have hSumPos : ∀ᵐ ω ∂P, 0 ≤ Term ω + Cash ω := by
    filter_upwards [hTermPos, hCashPos] with ω ht hc
    linarith
  exact AvramDividend.Classical.avram_p4_f4_positive_clock_real_to_ennreal_weighted_budget
    S (fun ω => Term ω + Cash ω) (w x) hwx hSumI hSumPos hMeanS
