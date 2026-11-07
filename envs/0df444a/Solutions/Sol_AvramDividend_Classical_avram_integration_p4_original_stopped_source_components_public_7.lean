-- Prove2me | solution 7 for AvramDividend.Classical.avram_integration_p4_original_stopped_source_components_public
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T08:12:21.632589+00:00
-- url     : https://prove2.me/submissions/f68a9ece-926d-4504-bab9-3bd006ca80c4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Probability.Process.Stopping
import Theorems.Thm_AvramDividend_Classical_avram_p4_f4_original_gaussian_only_centered_stopped_payoff_bound
import Theorems.Thm_AvramDividend_Classical_avram_p4_f4_original_purejump_centered_stopped_payoff_bound
import Theorems.Thm_AvramDividend_Classical_avram_p4_f4_original_five_witness_gaussian_plus_jump
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (q : ℝ) (hq : 0 < q)
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
    ∃ Mc Ms Ml G R : Ω → ℝ,
      Integrable Mc P ∧ Integrable Ms P ∧ Integrable Ml P ∧
      Integrable G P ∧
      (∫ ω, Mc ω ∂P) = 0 ∧
      (∫ ω, Ms ω ∂P) = 0 ∧
      (∫ ω, Ml ω ∂P) = 0 ∧
      (∀ᵐ ω ∂P, G ω ≤ 0) ∧
      (∀ᵐ ω ∂P, R ω ≤ 0) ∧
      (∀ᵐ ω ∂P, Term ω + Cash ω ≤
        w x + Mc ω + Ms ω + Ml ω + G ω + R ω) := by
  letI : IsProbabilityMeasure P := X.isProbability
  by_cases hν : X.ν = 0
  · obtain ⟨Mc, hMcI, hMc0, hBound⟩ :=
      avram_p4_f4_original_gaussian_only_centered_stopped_payoff_bound
        X hX hBV hν q hq w C hC hw0 hw_cont hw_neg hw_smooth hw_gen
        hw_grad x hx hxc D hD hw_nonneg hjump n hn τ hτeq hτmeas
        hτstop W Cash Term hW hCash hTerm hTermMeas hCashI
    refine ⟨Mc, (fun _ => 0), (fun _ => 0), (fun _ => 0),
      (fun _ => 0), hMcI, integrable_const (0 : ℝ),
      integrable_const (0 : ℝ), integrable_const (0 : ℝ),
      hMc0, ?_, ?_, ?_, ?_, ?_⟩
    · simp
    · simp
    · filter_upwards [] with ω
      simp
    · filter_upwards [] with ω
      simp
    · filter_upwards [hBound] with ω hω
      simpa only [add_zero, zero_add] using hω
  · by_cases hσ : X.σ = 0
    · obtain ⟨Ms, Ml, hMsI, hMlI, hMs0, hMl0, hBound⟩ :=
        avram_p4_f4_original_purejump_centered_stopped_payoff_bound
          X hX hBV hν hσ q hq w C hC hw0 hw_cont hw_neg hw_smooth hw_gen
          hw_grad x hx hxc D hD hw_nonneg hjump n hn τ hτeq hτmeas
          hτstop W Cash Term hW hCash hTerm hTermMeas hCashI
      refine ⟨(fun _ => 0), Ms, Ml, (fun _ => 0),
        (fun _ => 0), integrable_const (0 : ℝ),
        hMsI, hMlI, integrable_const (0 : ℝ),
        ?_, hMs0, hMl0, ?_, ?_, ?_⟩
      · simp
      · filter_upwards [] with ω
        simp
      · filter_upwards [] with ω
        simp
      · filter_upwards [hBound] with ω hω
        simpa only [add_zero, zero_add] using hω
    · exact avram_p4_f4_original_five_witness_gaussian_plus_jump
        X hX hBV hσ hν q hq w C hC hw0 hw_cont hw_neg hw_smooth hw_gen
        hw_grad x hx hxc D hD hw_nonneg hjump n hn τ hτeq hτmeas
        hτstop W Cash Term hW hCash hTerm hTermMeas hCashI
