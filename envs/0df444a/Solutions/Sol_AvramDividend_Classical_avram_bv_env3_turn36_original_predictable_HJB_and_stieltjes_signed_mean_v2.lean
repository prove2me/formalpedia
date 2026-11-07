-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_env3_turn36_original_predictable_HJB_and_stieltjes_signed_mean_v2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T06:47:09.528253+00:00
-- url     : https://prove2.me/submissions/3f0da41d-49c9-4322-9dac-1bfb03a61cfc

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_env3_turn33_original_predictable_prefix_generator_HJB_signed_budget_v2
import Theorems.Thm_AvramDividend_Classical_avram_bv_env3_turn35_original_controlled_dividend_gradient_density_nonpos
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
/-- Original physical generator, martingale, Stieltjes signed budget. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ)
    (C : ℝ≥0∞) (hC : 0 < C)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (U : ℝ≥0 × Ω → ℝ) (E : Set (ℝ≥0 × Ω))
    (hInterior : ∀ p ∈ E, 0 < U p ∧ ENNReal.ofReal (U p) < C)
    (B : Ω → Set ℝ)
    (hB : ∀ ω s, s ∈ B ω →
      0 < riskProcess X x D s.toNNReal ω ∧ ENNReal.ofReal (riskProcess X x D s.toNNReal ω) < C)
    (Y : ℝ≥0 → Ω → ℝ) (hMart : Martingale Y 𝓕.rightCont P)
    (u : ℕ → ℝ≥0) (hu : Monotone u) (m : ℕ)
    (k : Ω → ℕ) (hk : Measurable k) (hkBound : ∀ ω, k ω ≤ m)
    (hPredictable : ∀ i : ℕ, MeasurableSet[𝓕.rightCont (u i)] {ω : Ω | i < k ω})
    (μ : Measure ℝ≥0)
    (hBI : ∀ i : ℕ, Integrable (fun ω =>
      ∫ t in Ioc (u i) (u (i + 1)), (if (t, ω) ∈ E then
        Real.exp (-(q * (t : ℝ))) * (X.generator w (U (t, ω)) - q * w (U (t, ω))) else 0) ∂μ) P)
    (hGradInt : Integrable (fun ω =>
      ∫ s, if s ∈ B ω then Real.exp (-(q * s)) *
        (1 - deriv w (riskProcess X x D s.toNNReal ω)) else 0 ∂(dividendMeasure D ω)) P) :
    Integrable (fun ω =>
      (∑ i ∈ Finset.range (k ω), ((Y (u (i + 1)) ω - Y (u i) ω) +
        (∫ t in Ioc (u i) (u (i + 1)), (if (t, ω) ∈ E then
          Real.exp (-(q * (t : ℝ))) * (X.generator w (U (t, ω)) - q * w (U (t, ω)))
          else 0) ∂μ))) +
      (∫ s, if s ∈ B ω then Real.exp (-(q * s)) *
        (1 - deriv w (riskProcess X x D s.toNNReal ω))
        else 0 ∂(dividendMeasure D ω))) P ∧
    (∫ ω,
      (∑ i ∈ Finset.range (k ω), ((Y (u (i + 1)) ω - Y (u i) ω) +
        (∫ t in Ioc (u i) (u (i + 1)), (if (t, ω) ∈ E then
          Real.exp (-(q * (t : ℝ))) * (X.generator w (U (t, ω)) - q * w (U (t, ω)))
          else 0) ∂μ))) +
      (∫ s, if s ∈ B ω then Real.exp (-(q * s)) *
        (1 - deriv w (riskProcess X x D s.toNNReal ω))
        else 0 ∂(dividendMeasure D ω)) ∂P) ≤ 0 := by
  let A : Ω → ℝ := fun ω =>
    ∑ i ∈ Finset.range (k ω), ((Y (u (i + 1)) ω - Y (u i) ω) +
      (∫ t in Ioc (u i) (u (i + 1)), (if (t, ω) ∈ E then
        Real.exp (-(q * (t : ℝ))) * (X.generator w (U (t, ω)) - q * w (U (t, ω)))
        else 0) ∂μ))
  let G : Ω → ℝ := fun ω =>
    ∫ s, if s ∈ B ω then Real.exp (-(q * s)) *
      (1 - deriv w (riskProcess X x D s.toNNReal ω)) else 0 ∂(dividendMeasure D ω)
  have hA : Integrable A P ∧ (∫ ω, A ω ∂P) ≤ 0 := by
    simpa only [A] using
      (avram_bv_env3_turn33_original_predictable_prefix_generator_HJB_signed_budget_v2
        X q hq w C hC hw_gen U E hInterior Y hMart
        u hu m k hk hkBound hPredictable μ hBI)
  have hGneg (ω : Ω) : G ω ≤ 0 := by
    dsimp [G]
    apply integral_nonpos
    intro s
    exact avram_bv_env3_turn35_original_controlled_dividend_gradient_density_nonpos
      X w C hw_grad x D hD B hB q ω s
  have hG : Integrable G P := hGradInt
  have hGmean : (∫ ω, G ω ∂P) ≤ 0 := by
    apply integral_nonpos
    intro ω; exact hGneg ω
  change Integrable (fun ω => A ω + G ω) P ∧
    (∫ ω, A ω + G ω ∂P) ≤ 0
  refine ⟨hA.1.add hG, ?_⟩
  rw [integral_add hA.1 hG]
  exact add_nonpos hA.2 hGmean
