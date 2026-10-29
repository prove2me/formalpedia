-- Prove2me | solution 2 for AvramDividend.Classical.avram_ws01e_bf_new_exp_supremum_strict_positive_ae
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T23:11:23.322271+00:00
-- url     : https://prove2.me/submissions/41df02ae-8712-406e-8898-7a31ae1fc76c

import Mathlib
import Mathlib.Probability.Distributions.Exponential
import Definitions.Def_AvramDividend_Classical_Reflection
open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) (S : Ω → ℝ) (lam : ℝ)
    (hlam : 0 < lam) (hS : Measurable S)
    (hLaw : Measure.map S μ = expMeasure lam) :
    ∀ᵐ z ∂μ, 0 < S z := by
  rw [ae_iff]
  have h1 : {z | ¬ 0 < S z} = S ⁻¹' Iic 0 := by ext z; simp
  rw [h1, ← Measure.map_apply hS measurableSet_Iic, hLaw]
  have := isProbabilityMeasure_expMeasure hlam
  rw [← ofReal_cdf, cdf_expMeasure_eq hlam]
  simp
