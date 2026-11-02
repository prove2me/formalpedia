-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_ubv_original_liminf_clock_fatou_without_monotonicity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T15:01:20.64351+00:00
-- url     : https://prove2.me/submissions/6da01831-fe73-4071-8772-79afebffa130

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_ubv_original_ae_cofinal_stochastic_fatou_no_extra_nonneg
import Theorems.Thm_AvramDividend_Classical_paymentTimes_min_mono_horizon
import Theorems.Thm_fatou_liminf_nonmonotone_pointwise_upper_bound_a302087d

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
    (hw0 : 0 ≤ w 0)
    (hw_cont : ContinuousOn w (Ici 0))
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
    (τ : ℕ → Ω → ℝ≥0∞)
    (hτmeas : ∀ n, Measurable (τ n))
    (hτliminfAE : ∀ᵐ ω ∂P,
      (⨆ n : ℕ, ⨅ k : ℕ, τ (n + k) ω) = ruinTime X x D ω)
    (hBudget : ∀ n : ℕ,
      (∫⁻ ω, ∫⁻ t in paymentTimes (τ n ω) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
        ENNReal.ofReal (w x)) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
      ENNReal.ofReal (w x) := by
  classical
  let σ : ℕ → Ω → ℝ≥0∞ := fun n ω => ⨅ k : ℕ, τ (n + k) ω
  have hσmeas : ∀ n, Measurable (σ n) := by
    intro n
    exact Measurable.iInf (fun k => hτmeas (n + k))
  have hσmono : ∀ ω, Monotone (fun n => σ n ω) := by
    intro ω n m hnm
    refine le_iInf (fun k => ?_)
    have hindex : n + ((m - n) + k) = m + k := by omega
    have hle : σ n ω ≤ τ (n + ((m - n) + k)) ω :=
      iInf_le (fun j : ℕ => τ (n + j) ω) ((m - n) + k)
    simpa only [hindex] using hle
  have hσsupAE : ∀ᵐ ω ∂P, (⨆ n, σ n ω) = ruinTime X x D ω := by
    filter_upwards [hτliminfAE] with ω hω
    simpa only [σ] using hω
  have hσle : ∀ n ω, σ n ω ≤ τ n ω := by
    intro n ω
    change (⨅ k : ℕ, τ (n + k) ω) ≤ τ n ω
    simpa only [Nat.add_zero] using
      (iInf_le (fun k : ℕ => τ (n + k) ω) 0)
  have hσBudget : ∀ n : ℕ,
      (∫⁻ ω, ∫⁻ t in paymentTimes (σ n ω) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
        ENNReal.ofReal (w x) := fatou_liminf_nonmonotone_pointwise_upper_bound_a302087d (Ω := Ω) (mΩ := mΩ) (P := P) (𝓕 := 𝓕) (X := X) (hX := hX) (hBV := hBV) (q := q) (hq := hq) (w := w) (C := C) (hw0 := hw0) (hw_cont := hw_cont) (hw_neg := hw_neg) (hw_smooth := hw_smooth) (hw_gen := hw_gen) (hw_grad := hw_grad) (x := x) (hxc := hxc) (D := D) (hD := hD) (hjump := hjump) (T := T) (hT := hT) (τ := τ) (hτmeas := hτmeas) (hτliminfAE := hτliminfAE) (hBudget := hBudget) (hσmeas := hσmeas) (hσmono := hσmono) (hσsupAE := hσsupAE) (hσle := hσle)
  exact avram_wave5_ubv_original_ae_cofinal_stochastic_fatou_no_extra_nonneg
    X hX hBV q hq w C hw0 hw_cont hw_neg hw_smooth hw_gen hw_grad
    x hxc D hD hjump T hT σ hσmeas hσmono hσsupAE hσBudget
