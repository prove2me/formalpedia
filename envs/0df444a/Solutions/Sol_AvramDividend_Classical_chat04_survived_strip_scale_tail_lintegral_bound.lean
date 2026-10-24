-- Prove2me | solution 1 for AvramDividend.Classical.chat04_survived_strip_scale_tail_lintegral_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T16:39:56.928455+00:00
-- url     : https://prove2.me/submissions/b6963cef-4133-40d1-83d4-c35dd9b00f07

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat03_discounted_scale_terminal_bound
import Mathlib.Analysis.Complex.Exponential

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

attribute [local instance] Classical.propDecidable

/-- Exponentially small expected residual on fully surviving strip paths. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a x : ℝ) (N t : ℝ≥0) (hNt : N ≤ t) :
    (∫⁻ ω, if (∀ s : ℝ≥0, s ≤ t →
          0 ≤ x + X.X s ω ∧ x + X.X s ω ≤ a) then
       ENNReal.ofReal (Real.exp (-(q * (t : ℝ))) * W (x + X.X t ω))
      else 0 ∂P) ≤ ENNReal.ofReal (Real.exp (-(q * (N : ℝ))) * W a) := by
  letI : IsProbabilityMeasure P := X.isProbability
  calc
    (∫⁻ ω, if (∀ s : ℝ≥0, s ≤ t →
          0 ≤ x + X.X s ω ∧ x + X.X s ω ≤ a) then
       ENNReal.ofReal (Real.exp (-(q * (t : ℝ))) * W (x + X.X t ω))
      else 0 ∂P) ≤
        ∫⁻ _ : Ω, ENNReal.ofReal (Real.exp (-(q * (N : ℝ))) * W a) ∂P := by
      apply lintegral_mono
      intro ω
      by_cases h : (∀ s : ℝ≥0, s ≤ t →
          0 ≤ x + X.X s ω ∧ x + X.X s ω ≤ a)
      · simp only [if_pos h]
        have ht := h t le_rfl
        exact ENNReal.ofReal_le_ofReal
          (chat03_discounted_scale_terminal_bound X q hq W hW a
            (x + X.X t ω) ht.1 ht.2 N t hNt)
      · simp only [if_neg h]
        exact bot_le
    _ = ENNReal.ofReal (Real.exp (-(q * (N : ℝ))) * W a) := by simp
