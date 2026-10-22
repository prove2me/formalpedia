-- Prove2me | solution 1 for AvramDividend.Classical.gaussian_double_tail_positive_tail_L1_lipschitz
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T20:43:55.773378+00:00
-- url     : https://prove2.me/submissions/1568a585-9d5f-4f4a-8fe8-211bca420913

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.Tactic.FunProp
import Theorems.Thm_AvramDividend_Classical_gaussian_double_tail_conditional_atom_lipschitz
import Theorems.Thm_AvramDividend_Classical_gaussian_esscher_positive_tail_weight_finite
import Mathlib.Analysis.Complex.Exponential

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped ENNReal
open AvramDividend.Classical

/-- The conditional Gaussian double-tail atom is L1-Lipschitz in time on
each fixed positive jump tail, with a finite Esscher-weighted constant. -/
theorem solution (μ : Measure ℝ) (ε φ s t : ℝ)
    (hε : 0 < ε) (hφ : 0 < φ)
    (hs : ε ≤ s) (ht : ε ≤ t)
    (hlevy : (∫⁻ z in Ioi (0 : ℝ),
      ENNReal.ofReal (min 1 (z ^ 2)) ∂μ) < ⊤) :
    (∫⁻ z in Ici ε, ENNReal.ofReal
      (|(if 0 < t ∧ t < z then (z - t) * Real.exp (-φ * z) else 0) -
        (if 0 < s ∧ s < z then (z - s) * Real.exp (-φ * z) else 0)|) ∂μ) ≤
    ENNReal.ofReal (|t - s|) *
      (∫⁻ z in Ici ε, ENNReal.ofReal (Real.exp (-φ * z)) ∂μ) ∧
    ENNReal.ofReal (|t - s|) *
      (∫⁻ z in Ici ε, ENNReal.ofReal (Real.exp (-φ * z)) ∂μ) < ⊤ := by
  have hs0 : 0 < s := lt_of_lt_of_le hε hs
  have ht0 : 0 < t := lt_of_lt_of_le hε ht
  have hmeas : Measurable (fun z : ℝ =>
      ENNReal.ofReal (Real.exp (-φ * z))) := by fun_prop
  have hpoint (z : ℝ) :
      ENNReal.ofReal
        (|(if 0 < t ∧ t < z then (z - t) * Real.exp (-φ * z) else 0) -
          (if 0 < s ∧ s < z then (z - s) * Real.exp (-φ * z) else 0)|) ≤
      ENNReal.ofReal (|t - s|) *
        ENNReal.ofReal (Real.exp (-φ * z)) := by
    rw [← ENNReal.ofReal_mul (abs_nonneg (t - s))]
    exact ENNReal.ofReal_le_ofReal
      (gaussian_double_tail_conditional_atom_lipschitz φ z s t hs0 ht0)
  constructor
  · calc
      (∫⁻ z in Ici ε, ENNReal.ofReal
        (|(if 0 < t ∧ t < z then (z - t) * Real.exp (-φ * z) else 0) -
          (if 0 < s ∧ s < z then (z - s) * Real.exp (-φ * z) else 0)|) ∂μ) ≤
        (∫⁻ z in Ici ε,
          ENNReal.ofReal (|t - s|) *
            ENNReal.ofReal (Real.exp (-φ * z)) ∂μ) := by
          apply lintegral_mono
          intro z
          exact hpoint z
      _ = _ := lintegral_const_mul (ENNReal.ofReal (|t - s|)) hmeas
  · apply ENNReal.mul_lt_top
    · exact ENNReal.ofReal_lt_top
    · exact gaussian_esscher_positive_tail_weight_finite μ ε φ hε hφ hlevy
