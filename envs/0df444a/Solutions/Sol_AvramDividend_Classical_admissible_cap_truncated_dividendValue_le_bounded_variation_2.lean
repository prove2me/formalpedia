-- Prove2me | solution 2 for AvramDividend.Classical.admissible_cap_truncated_dividendValue_le_bounded_variation
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T20:58:27.52592+00:00
-- url     : https://prove2.me/submissions/c528124a-ed76-4892-893c-9b7e49fcadcc
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_hjb_pointwise_inequalities
import Theorems.Thm_AvramDividend_Classical_verification_candidate_nonneg_before_ruin
import Theorems.Thm_AvramDividend_Classical_verification_strategy_lump_sum_drop
import Theorems.Thm_AvramDividend_Classical_admissible_cap_truncated_bv_stochastic_core

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_hjb : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧
        max (X.generator w y - q * w y) (1 - deriv w y) = 0)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (T : ℝ) (hT : 0 ≤ T) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
      ENNReal.ofReal (w x) := by
  have hgen :
      ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
        X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0 := by
    intro y hy hyC
    have h := hw_hjb y hy hyC
    exact ⟨h.1, (hjb_pointwise_inequalities X q w y h.2).1⟩
  have hgrad :
      ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y := by
    intro y hy hyC
    exact (hjb_pointwise_inequalities X q w y (hw_hjb y hy hyC).2).2
  have hsmooth :
      (¬ X.BoundedVariation →
        ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) ∧
      (X.BoundedVariation →
        ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) := by
    constructor
    · intro h
      exact (h hBV).elim
    · intro _
      exact hw_smooth
  have hnonneg :
      ∀ ω (t : ℝ≥0), 0 < t →
        (t : ℝ≥0∞) < ruinTime X x D ω →
        0 ≤ w (riskProcess X x D t ω) := by
    intro ω t ht htru
    exact verification_candidate_nonneg_before_ruin
      X q w C hw_cont hw0 hsmooth hw_hjb x D hD ω t ht htru
  have hdiff :
      DifferentiableOn ℝ w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} :=
    hw_smooth.differentiableOn (by norm_num)
  have hjump :
      ∀ ω (t : ℝ≥0),
        (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
        rightLimit D t ω - D t ω ≤
          w (riskProcess X x D t ω) -
            w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)) := by
    intro ω t ht
    exact verification_strategy_lump_sum_drop
      X w C hw_cont hdiff hgrad x hxc D hD ω t ht
  exact admissible_cap_truncated_bv_stochastic_core
    X hX hBV q hq w C hw_cont hw_neg hw_smooth
    hgen hgrad x hxc D hD hnonneg hjump T hT
