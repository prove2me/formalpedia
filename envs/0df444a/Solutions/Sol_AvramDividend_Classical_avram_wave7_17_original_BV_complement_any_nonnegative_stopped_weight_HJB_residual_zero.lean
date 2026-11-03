-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_17_original_BV_complement_any_nonnegative_stopped_weight_HJB_residual_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T20:33:46.509592+00:00
-- url     : https://prove2.me/submissions/9edcd1f6-c11b-48ad-a78c-12fb096f6426

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_17_original_BV_strict_complement_sharp_drift_budget
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_BV_predictable_discounted_generator_gradient_envelope
import Theorems.Thm_AvramDividend_Classical_avram_wave7_17_original_BV_ruin_stopped_strict_interior_measurable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- Any nonnegative random localisation weight preserves zero positive
discounted HJB drift and negative Lévy-mark generator residual. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (H : ℝ) (hH : 0 ≤ H)
    (hEnvelope : ¬ (x + H * X.drift ≤ w x))
    (T : ℝ≥0)
    (ρ : ℝ≥0 × Ω → ℝ) (hρ : ∀ p, 0 ≤ ρ p) :
    let μ : Measure (ℝ≥0 × Ω) :=
      ((((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map Real.toNNReal).prod P)
    let Y : ℝ≥0 × Ω → ℝ := fun p =>
      Function.leftLim (fun t : ℝ≥0 =>
        x + X.X t p.2 - rightLimit D t p.2) p.1
    let S : Set (ℝ≥0 × Ω) :=
      {p | p.1 ≤ T ∧ (p.1 : ℝ≥0∞) < ruinTime X x D p.2 ∧
        0 < Y p ∧ ENNReal.ofReal (Y p) < C}
    (∫⁻ p in S, ENNReal.ofReal
      (ρ p * Real.exp (-(q * (p.1 : ℝ))) *
        (X.drift + (∫ z in Iio (0 : ℝ),
          w (Y p + z) - w (Y p) ∂X.ν) - q * w (Y p))) ∂μ) = 0 := by
  dsimp only
  let μ : Measure (ℝ≥0 × Ω) :=
    ((((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map Real.toNNReal).prod P)
  let Y : ℝ≥0 × Ω → ℝ := fun p =>
    Function.leftLim (fun t : ℝ≥0 =>
      x + X.X t p.2 - rightLimit D t p.2) p.1
  let S : Set (ℝ≥0 × Ω) :=
    {p | p.1 ≤ T ∧ (p.1 : ℝ≥0∞) < ruinTime X x D p.2 ∧
      0 < Y p ∧ ENNReal.ofReal (Y p) < C}
  have hS : MeasurableSet S :=
    avram_wave7_17_original_BV_ruin_stopped_strict_interior_measurable
      X x D hD.1.1 T C
  have hdpos : 0 < X.drift := by
    obtain ⟨_, hd, _, _⟩ :=
      avram_wave7_17_original_BV_strict_complement_sharp_drift_budget
        X hX hBV q hq w C hC hw_cont hw0 hw_smooth hw_grad
        x hx hxc D hD H hH hEnvelope
    exact hd
  have hz : (fun p : ℝ≥0 × Ω => ENNReal.ofReal
      (ρ p * Real.exp (-(q * (p.1 : ℝ))) *
        (X.drift + (∫ z in Iio (0 : ℝ),
          w (Y p + z) - w (Y p) ∂X.ν) - q * w (Y p)))) =ᵐ[μ.restrict S]
      (fun _ => (0 : ℝ≥0∞)) := by
    filter_upwards [ae_restrict_mem hS] with p hp
    rcases hp with ⟨_, _, hy0, hyC⟩
    have hSign :=
      avram_wave7_02_original_BV_predictable_discounted_generator_gradient_envelope
        X hBV q w C hw_gen hw_grad x D p.2 p.1 ⟨hy0, hyC⟩
    dsimp only at hSign
    obtain ⟨_, hGenSign, _⟩ := hSign
    have hGrad : 1 ≤ deriv w (Y p) := hw_grad (Y p) hy0 hyC
    have hMul : X.drift ≤ X.drift * deriv w (Y p) := by
      calc
        X.drift = X.drift * 1 := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hGrad (le_of_lt hdpos)
    have hExp : 0 ≤ Real.exp (-(q * (p.1 : ℝ))) :=
      le_of_lt (Real.exp_pos _)
    have hWeighted := mul_le_mul_of_nonneg_left hMul hExp
    have hRes : Real.exp (-(q * (p.1 : ℝ))) *
      (X.drift + (∫ z in Iio (0 : ℝ),
        w (Y p + z) - w (Y p) ∂X.ν) - q * w (Y p)) ≤ 0 := by
      dsimp only [Y] at hGenSign hWeighted
      nlinarith
    have hFinal : ρ p * Real.exp (-(q * (p.1 : ℝ))) *
      (X.drift + (∫ z in Iio (0 : ℝ),
        w (Y p + z) - w (Y p) ∂X.ν) - q * w (Y p)) ≤ 0 := by
      nlinarith [mul_nonpos_of_nonneg_of_nonpos (hρ p) hRes]
    exact ENNReal.ofReal_eq_zero.mpr hFinal
  calc
    (∫⁻ p in S, ENNReal.ofReal
      (ρ p * Real.exp (-(q * (p.1 : ℝ))) *
        (X.drift + (∫ z in Iio (0 : ℝ),
          w (Y p + z) - w (Y p) ∂X.ν) - q * w (Y p))) ∂μ) =
      (∫⁻ p in S, (0 : ℝ≥0∞) ∂μ) := lintegral_congr_ae hz
    _ = 0 := by simp
