-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_ubv_original_overshooting_liminf_fatou_no_extra_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T15:31:34.679733+00:00
-- url     : https://prove2.me/submissions/8e904922-acc5-4d9d-9a32-1d7d260ac4e1

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_ruinTime_measurable
import Theorems.Thm_AvramDividend_Classical_paymentTimes_min_mono_horizon
import Theorems.Thm_AvramDividend_Classical_avram_wave5_ubv_original_liminf_clock_fatou_without_monotonicity
import Theorems.Thm_fatou_overshoot_liminf_identity_2c381a88

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
    (hBV : ¬ X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (T : ℝ) (hT : 0 ≤ T)
    (τ : ℕ → Ω → ℝ≥0∞) (hτmeas : ∀ n, Measurable (τ n))
    (hτliminfLowerAE : ∀ᵐ ω ∂P,
      ruinTime X x D ω ≤ (⨆ n : ℕ, ⨅ k : ℕ, τ (n + k) ω))
    (hBudget : ∀ n : ℕ,
      (∫⁻ ω, ∫⁻ t in paymentTimes (τ n ω) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
        ENNReal.ofReal (w x)) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
      ENNReal.ofReal (w x) := by
  let σ : ℕ → Ω → ℝ≥0∞ := fun n ω => min (ruinTime X x D ω) (τ n ω)
  have hσmeas : ∀ n, Measurable (σ n) :=
    fun n => (ruinTime_measurable X x D hD.1.1).min (hτmeas n)
  have hσliminfAE : ∀ᵐ ω ∂P,
      (⨆ n : ℕ, ⨅ k : ℕ, σ (n + k) ω) = ruinTime X x D ω := fatou_overshoot_liminf_identity_2c381a88 (Ω := Ω) (mΩ := mΩ) (P := P) (𝓕 := 𝓕) (X := X) (hX := hX) (hBV := hBV) (q := q) (hq := hq) (w := w) (C := C) (hw0 := hw0) (hw_cont := hw_cont) (hw_neg := hw_neg) (hw_smooth := hw_smooth) (hw_gen := hw_gen) (hw_grad := hw_grad) (x := x) (hxc := hxc) (D := D) (hD := hD) (hjump := hjump) (T := T) (hT := hT) (τ := τ) (hτmeas := hτmeas) (hτliminfLowerAE := hτliminfLowerAE) (hBudget := hBudget) (hσmeas := hσmeas)
  have hσBudget : ∀ n : ℕ,
      (∫⁻ ω, ∫⁻ t in paymentTimes (σ n ω) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
        ENNReal.ofReal (w x) := by
    intro n
    calc
      (∫⁻ ω, ∫⁻ t in paymentTimes (σ n ω) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
        (∫⁻ ω, ∫⁻ t in paymentTimes (τ n ω) ∩ Iic T,
          ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) := by
            apply lintegral_mono
            intro ω
            apply lintegral_mono_set
            intro t ht
            have hs : paymentTimes (σ n ω) ⊆ paymentTimes (τ n ω) := by
              simpa using paymentTimes_min_mono_horizon
                ⊤ (σ n ω) (τ n ω) (min_le_right _ _)
            exact ⟨hs ht.1, ht.2⟩
      _ ≤ ENNReal.ofReal (w x) := hBudget n
  exact avram_wave5_ubv_original_liminf_clock_fatou_without_monotonicity
    X hX hBV q hq w C hw0 hw_cont hw_neg hw_smooth hw_gen hw_grad
    x hxc D hD hjump T hT σ hσmeas hσliminfAE hσBudget
end
