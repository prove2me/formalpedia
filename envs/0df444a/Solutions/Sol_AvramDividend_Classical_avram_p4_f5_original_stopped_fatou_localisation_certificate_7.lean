-- Prove2me | solution 7 for AvramDividend.Classical.avram_p4_f5_original_stopped_fatou_localisation_certificate
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T00:11:32.973207+00:00
-- url     : https://prove2.me/submissions/499d8f5d-15b9-42a4-bf26-47503461afcb
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Probability.Process.Stopping
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_f6_original_compact_clock_exact_payoff_convergence
import Theorems.Thm_AvramDividend_Classical_avram_p4_f8_original_positive_clock_masked_HJB_expected_upper
import Theorems.Thm_AvramDividend_Classical_avram_ubv_loc6_original_zero_clock_exact_physical_F_le

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy
  P 𝓕) (hX : X.Standing) (hBV : ¬ X.BoundedVariation) (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hw0 : 0 ≤
  w 0) (hw_cont : ContinuousOn w (Ici 0)) (hw_neg : ∀ y < 0, w y = 0) (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧
  ENNReal.ofReal y < C}) (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → X.GeneratorIntegrable w y ∧ X.generator w y - q
  * w y ≤ 0) (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y) (x : ℝ) (hx : 0 < x) (hxc : ENNReal.ofReal
  x ≤ C) (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D) (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t → (t : ℝ≥0∞) < ruinTime X x D ω
  → 0 ≤ w (riskProcess X x D t ω)) (hjump : ∀ ω (t : ℝ≥0), (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) → rightLimit D t ω - D
  t ω ≤ w (riskProcess X x D t ω) - w (riskProcess X x D t ω - (rightLimit D t ω - D t ω))) (n : ℕ) (hn : 0 < n) (τ : Ω →
  ℝ≥0) (hτeq : ∀ ω, τ ω = (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal) (hτmeas : Measurable (fun ω => (τ ω : ℝ))) (hτstop
  : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0))) (W Cash Term : Ω → ℝ) (hW : ∀ ω, W ω = if τ ω = 0 ∨ (τ ω :
  ℝ≥0∞) < ruinTime X x D ω then x + X.X (τ ω) ω - rightLimit D (τ ω) ω else riskProcess X x D (τ ω) ω) (hCash : ∀ ω, Cash
  ω = (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ), ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D
  ω)).toReal) (hTerm : ∀ ω, Term ω = Real.exp (-(q * (τ ω : ℝ))) * w (W ω)) (hTermMeas : AEStronglyMeasurable Term P)
  (hCashI : Integrable Cash P) : ∃ (σ : ℕ → Ω → ℝ≥0) (F : ℕ → Ω → ℝ), 0 ≤ w x ∧ (∀ k, IsStoppingTime 𝓕.rightCont (fun ω =>
  (σ k ω : WithTop ℝ≥0))) ∧ (∀ k ω, σ k ω ≤ τ ω) ∧ (∀ k ω, F k ω = Real.exp (-(q * (σ k ω : ℝ))) * w (if σ k ω = 0 ∨ (σ k
  ω : ℝ≥0∞) < ruinTime X x D ω then x + X.X (σ k ω) ω - rightLimit D (σ k ω) ω else riskProcess X x D (σ k ω) ω) + (∫⁻ s
  in paymentTimes (ruinTime X x D ω) ∩ Iic (σ k ω : ℝ), ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D
  ω)).toReal) ∧ (∀ k, Measurable (F k)) ∧ (∀ k, Integrable (F k) P) ∧ (∀ k, 0 ≤ᵐ[P] F k) ∧ (∀ᵐ ω ∂P, Tendsto (fun k =>
  ENNReal.ofReal (F k ω)) atTop (𝓝 (ENNReal.ofReal (Term ω + Cash ω)))) ∧ (∀ k, (∫ ω, F k ω ∂P) ≤ w x) := by
  obtain ⟨σ, F, hwx, hStop, hBound, hExact, hMeas, hInt, hNonneg, hConv⟩ :=
    avram_f6_original_compact_clock_exact_payoff_convergence
      X hX hBV q hq w C hC hw0 hw_cont hw_neg
      hw_smooth hw_gen hw_grad x hx hxc D hD hw_nonneg hjump
      n hn τ hτeq hτmeas hτstop W Cash Term hW hCash hTerm
      hTermMeas hCashI
  refine ⟨σ, F, hwx, hStop, hBound, hExact, hMeas, hInt,
    hNonneg, hConv, ?_⟩
  intro k
  obtain ⟨hMaskInt, hMaskUpper⟩ :=
    avram_p4_f8_original_positive_clock_masked_HJB_expected_upper
      X hX hBV q hq w C hC hw0 hw_cont hw_neg
      hw_smooth hw_gen hw_grad x hx hxc D hD hw_nonneg hjump
      n hn τ hτeq hτmeas hτstop W Cash Term hW hCash hTerm
      hTermMeas hCashI σ F hStop hBound hExact hInt k
  have hMono : (∫ ω, F k ω ∂P) ≤
      (∫ ω, if σ k ω = 0 then w x else F k ω ∂P) := by
    refine integral_mono_ae (hInt k) hMaskInt ?_
    filter_upwards [] with ω
    by_cases hzero : σ k ω = 0
    · simpa [hzero] using
        (avram_ubv_loc6_original_zero_clock_exact_physical_F_le
          X x q w C D hD hjump σ F hExact k ω hzero)
    · simp [hzero]
  exact hMono.trans hMaskUpper
