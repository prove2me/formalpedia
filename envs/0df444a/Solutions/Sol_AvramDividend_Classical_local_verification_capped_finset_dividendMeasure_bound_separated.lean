-- Prove2me | solution 1 for AvramDividend.Classical.local_verification_capped_finset_dividendMeasure_bound_separated
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T23:03:24.570673+00:00
-- url     : https://prove2.me/submissions/d0d61f64-6c93-4e42-88d5-ccec74731459

import Mathlib
import Theorems.Thm_AvramDividend_Classical_local_verification_capped_countable_dividendMeasure_bound_separated
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
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
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth :
      (¬ X.BoundedVariation →
        ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) ∧
      (X.BoundedVariation →
        ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}))
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hxC : ENNReal.ofReal x ≤ C)
    (ω : Ω) (S : Finset ℝ)
    (hNonneg : ∀ s ∈ S, 0 ≤ s)
    (hActive : ∀ s ∈ S,
      s.toNNReal = 0 ∨ (s.toNNReal : ℝ≥0∞) < ruinTime X x D ω) :
    (∫⁻ s in (S : Set ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)) ≤
    ∑ s ∈ S, ENNReal.ofReal (Real.exp (-(q * s)) *
      (w (riskProcess X x D s.toNNReal ω) -
        w (riskProcess X x D s.toNNReal ω -
          (rightLimit D s.toNNReal ω - D s.toNNReal ω)))) := by
  have hcount : (S : Set ℝ).Countable := S.finite_toSet.countable
  have h :=
    AvramDividend.Classical.local_verification_capped_countable_dividendMeasure_bound_separated
      X x q w C hw_cont hw_smooth hw_gen hw_grad D hD hxC ω
      (S : Set ℝ) hcount
      (by
        intro s hs
        exact hNonneg s hs)
      (by
        intro s hs
        exact hActive s hs)
  simpa only [← Finset.tsum_subtype'] using h
