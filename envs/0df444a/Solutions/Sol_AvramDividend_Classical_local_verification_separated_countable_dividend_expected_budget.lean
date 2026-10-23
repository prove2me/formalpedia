-- Prove2me | solution 1 for AvramDividend.Classical.local_verification_separated_countable_dividend_expected_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T22:37:00.260048+00:00
-- url     : https://prove2.me/submissions/67018ded-3872-44b9-80f9-a0228521c927

import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_local_verification_capped_countable_dividendMeasure_bound_separated
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hq : 0 < q)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth :
      (¬ X.BoundedVariation →
        ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) ∧
      (X.BoundedVariation →
        ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}))
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (hw_nonneg : ∀ y : ℝ, 0 ≤ y → ENNReal.ofReal y ≤ C → 0 ≤ w y)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hxC : ENNReal.ofReal x ≤ C)
    (S : Ω → Set ℝ)
    (hCountable : ∀ ω, (S ω).Countable)
    (hNonneg : ∀ ω s, s ∈ S ω → 0 ≤ s)
    (hActive : ∀ ω s, s ∈ S ω →
      s.toNNReal = 0 ∨ (s.toNNReal : ℝ≥0∞) < ruinTime X x D ω)
    (hExpectedDropBudget :
      (∫⁻ ω, ∑' s : S ω,
        ENNReal.ofReal (Real.exp (-(q * (s : ℝ))) *
          (w (riskProcess X x D (s : ℝ).toNNReal ω) -
            w (riskProcess X x D (s : ℝ).toNNReal ω -
              (rightLimit D (s : ℝ).toNNReal ω - D (s : ℝ).toNNReal ω)))) ∂P)
        ≤ ENNReal.ofReal (w x)) :
    (∫⁻ ω, ∫⁻ s in S ω,
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω) ∂P)
      ≤ ENNReal.ofReal (w x)  := by
  calc
    (∫⁻ ω, ∫⁻ s in S ω,
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω) ∂P) ≤
        (∫⁻ ω, ∑' s : S ω,
          ENNReal.ofReal (Real.exp (-(q * (s : ℝ))) *
            (w (riskProcess X x D (s : ℝ).toNNReal ω) -
              w (riskProcess X x D (s : ℝ).toNNReal ω -
                (rightLimit D (s : ℝ).toNNReal ω - D (s : ℝ).toNNReal ω)))) ∂P) := by
      apply lintegral_mono
      intro ω
      exact AvramDividend.Classical.local_verification_capped_countable_dividendMeasure_bound_separated
        X x q w C hw_cont hw_smooth hw_gen hw_grad D hD hxC ω (S ω)
          (hCountable ω) (hNonneg ω) (hActive ω)
    _ ≤ ENNReal.ofReal (w x) := hExpectedDropBudget

