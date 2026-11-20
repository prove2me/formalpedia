-- Prove2me | solution 1 for AvramDividend.Classical.avram_f6_zero_nu_finitecap_exact_clock_HJB_expected_upper
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T19:56:31.744992+00:00
-- url     : https://prove2.me/submissions/f810785c-922c-4efa-b5ca-d2599f82ef55
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_loc6_zero_nu_finitecap_positive_clock_gaussian_ito
import Theorems.Thm_AvramDividend_Classical_avram_ubv_loc6_original_zero_clock_exact_physical_F_le
set_option autoImplicit false
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution {Ω :
    Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} (X :
    SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (hBV : ¬ X.BoundedVariation) (q : ℝ) (hq : 0
    < q) (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0) (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y
    < C}) (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → X.GeneratorIntegrable w y ∧
    X.generator w y - q * w y ≤ 0) (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv
    w y) (x : ℝ) (hx : 0 < x) (hxc : ENNReal.ofReal x ≤ C) (D : ℝ≥0 → Ω → ℝ) (hD :
    IsAdmissibleLe X x C D) (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t → (t : ℝ≥0∞) < ruinTime X x D ω →
    0 ≤ w (riskProcess X x D t ω)) (hjump : ∀ ω (t : ℝ≥0), (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D
    ω) → rightLimit D t ω - D t ω ≤ w (riskProcess X x D t ω) - w (riskProcess X x D t ω -
    (rightLimit D t ω - D t ω))) (n : ℕ) (hn : 0 < n) (τ : Ω → ℝ≥0) (hτeq : ∀ ω, τ ω = (min
    (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal) (hτmeas : Measurable (fun ω => (τ ω : ℝ))) (hτstop
    : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0))) (W Cash Term : Ω → ℝ) (hW : ∀
    ω, W ω = if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω then x + X.X (τ ω) ω - rightLimit D
    (τ ω) ω else riskProcess X x D (τ ω) ω) (hCash : ∀ ω, Cash ω = (∫⁻ s in paymentTimes
    (ruinTime X x D ω) ∩ Iic (τ ω : ℝ), ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure
    D ω)).toReal) (hTerm : ∀ ω, Term ω = Real.exp (-(q * (τ ω : ℝ))) * w (W ω)) (hTermMeas :
    AEStronglyMeasurable Term P) (hCashI : Integrable Cash P) (σ : ℕ → Ω → ℝ≥0) (F : ℕ → Ω → ℝ)
    (hσstop : ∀ k, IsStoppingTime 𝓕.rightCont (fun ω => (σ k ω : WithTop ℝ≥0))) (hσle : ∀ k ω,
    σ k ω ≤ τ ω) (hFsource : ∀ k ω, F k ω = Real.exp (-(q * (σ k ω : ℝ))) * w (if σ k ω = 0 ∨
    (σ k ω : ℝ≥0∞) < ruinTime X x D ω then x + X.X (σ k ω) ω - rightLimit D (σ k ω) ω else
    riskProcess X x D (σ k ω) ω) + (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σ k ω : ℝ),
    ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal) (hFI : ∀ k, Integrable
    (F k) P) (hν : X.ν = 0) (hFinite : C ≠ ⊤) :
    ∀ k, (∫ ω, F k ω ∂P) ≤ w x  := by
  letI : IsProbabilityMeasure P := X.isProbability
  intro k
  obtain ⟨Mc, G, R, hMc, hMzero, hM0, hG, hR, hPos⟩ :=
    avram_ubv_loc6_zero_nu_finitecap_positive_clock_gaussian_ito
      X hX hBV hν q hq w C hC hFinite hw0 hw_cont hw_neg
      hw_smooth hw_gen hw_grad x hx hxc D hD hw_nonneg hjump
      n hn τ hτeq hτmeas hτstop W Cash Term hW hCash
      hTerm hTermMeas hCashI σ F hσstop hσle hFsource hFI k
  have hBound : ∀ᵐ ω ∂P, F k ω ≤ w x + Mc ω := by
    filter_upwards [hG, hR, hPos] with ω hg hr hpos
    by_cases hz : σ k ω = 0
    · have hf := avram_ubv_loc6_original_zero_clock_exact_physical_F_le
        X x q w C D hD hjump σ F hFsource k ω hz
      rw [hM0 ω hz]
      simpa using hf
    · have hf := hpos hz
      linarith
  have hI : Integrable (fun ω => w x + Mc ω) P :=
    (integrable_const (w x)).add hMc
  calc
    ∫ ω, F k ω ∂P ≤ ∫ ω, w x + Mc ω ∂P :=
      integral_mono_ae (hFI k) hI hBound
    _ = (∫ _ : Ω, w x ∂P) + ∫ ω, Mc ω ∂P := by
      exact integral_add (integrable_const _) hMc
    _ = w x := by simp [hMzero]
