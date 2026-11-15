-- Prove2me | solution 1 for AvramDividend.Classical.avram_b24_original_zero_clock_ruinclipped_full_Iic_cash_initial_condexp_upper
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T21:27:07.5678+00:00
-- url     : https://prove2.me/submissions/e3db5f0f-d082-4c72-bc40-e2dab5cf6010

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_hor3_original_zero_clock_term_cash_pathwise_le
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} (X :
    SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (hBV : ¬ X.BoundedVariation) (hν : X.ν ≠ 0) (hσ
    : X.σ ≠ 0) (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hw0 : 0 ≤ w 0) (hw_cont
    : ContinuousOn w (Ici 0)) (hw_neg : ∀ y < 0, w y = 0) (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ |
    0 < y ∧ ENNReal.ofReal y < C}) (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
    X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0) (hw_grad : ∀ y : ℝ, 0 < y →
    ENNReal.ofReal y < C → 1 ≤ deriv w y) (x : ℝ) (hx : 0 < x) (hxc : ENNReal.ofReal x ≤ C) (D :
    ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D) (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t → (t : ℝ≥0∞) <
    ruinTime X x D ω → 0 ≤ w (riskProcess X x D t ω)) (hjump : ∀ ω (t : ℝ≥0), (t = 0 ∨ (t : ℝ≥0∞)
    < ruinTime X x D ω) → rightLimit D t ω - D t ω ≤ w (riskProcess X x D t ω) - w (riskProcess X
    x D t ω - (rightLimit D t ω - D t ω))) (n : ℕ) (hn : 0 < n) (σ : Ω → ℝ≥0) (hσstop :
    IsStoppingTime 𝓕.rightCont (fun ω => (σ ω : WithTop ℝ≥0))) (hσbound : ∀ ω, σ ω ≤ (n : ℝ≥0))
    (hσclip : ∀ ω, σ ω ≤ (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal) (F : Ω → ℝ) (hFsource : ∀
    ω, F ω = Real.exp (-(q * (σ ω : ℝ))) * w (if σ ω = 0 ∨ (σ ω : ℝ≥0∞) < ruinTime X x D ω then x
    + X.X (σ ω) ω - rightLimit D (σ ω) ω else riskProcess X x D (σ ω) ω) + (∫⁻ s in paymentTimes
    (ruinTime X x D ω) ∩ Iic (σ ω : ℝ), ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D
    ω)).toReal) (hFI : Integrable F P) (hFiniteActivity : X.ν (Iio (0 : ℝ)) ≠ ⊤) (hσzero : ∀ᵐ ω
    ∂P, σ ω = 0) :
    ∀ᵐ ω ∂P, condExp (𝓕.rightCont 0) P F ω ≤ w x  := by
  letI : IsProbabilityMeasure P := X.isProbability
  let W : Ω → ℝ := fun ω =>
    if σ ω = 0 ∨ (σ ω : ℝ≥0∞) < ruinTime X x D ω then
      x + X.X (σ ω) ω - rightLimit D (σ ω) ω
    else riskProcess X x D (σ ω) ω
  let Cash : Ω → ℝ := fun ω =>
    (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal
  let Term : Ω → ℝ := fun ω =>
    Real.exp (-(q * (σ ω : ℝ))) * w (W ω)
  have hFBound : F ≤ᵐ[P] (fun _ : Ω => w x) := by
    filter_upwards [hσzero] with ω hZero
    have hZ := avram_ubv_hor3_original_zero_clock_term_cash_pathwise_le
      X x q w C D hD hjump σ W Cash Term
      (fun ω => rfl) (fun ω => rfl) (fun ω => rfl) ω hZero
    have hEq : F ω = Term ω + Cash ω := by
      simpa only [Term, Cash, W] using hFsource ω
    simpa only [hEq] using hZ
  have hCE := condExp_mono (m := 𝓕.rightCont 0)
    hFI (integrable_const (w x)) hFBound
  have hConst :
      condExp (𝓕.rightCont 0) P (fun _ : Ω => w x) =
        (fun _ : Ω => w x) :=
    condExp_const (𝓕.rightCont.le 0) (w x)
  rw [hConst] at hCE
  exact hCE
