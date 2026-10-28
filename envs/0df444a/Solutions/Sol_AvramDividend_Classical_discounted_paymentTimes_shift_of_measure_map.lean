-- Prove2me | solution 1 for AvramDividend.Classical.discounted_paymentTimes_shift_of_measure_map
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T10:52:35.543717+00:00
-- url     : https://prove2.me/submissions/63151f9d-6724-42b2-93fc-35f4d79af704

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Theorems.Thm_AvramDividend_Classical_paymentTimes_measurable
import Theorems.Thm_AvramDividend_Classical_lintegral_killed_discount_translation_of_measure_map
import Mathlib.Analysis.Complex.Exponential
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    (μ ν : Measure ℝ) (u q : ℝ) (σ : ℝ≥0∞)
    (hμ : μ = Measure.map (fun t : ℝ => u + t) ν) :
    (∫⁻ t in Set.Ioi u ∩ paymentTimes σ,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂μ) =
    ENNReal.ofReal (Real.exp (-(q * u))) *
      (∫⁻ t in Set.Ioi (0 : ℝ) ∩
          ((fun t : ℝ => u + t) ⁻¹' paymentTimes σ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂ν) := by
  have hshift : Measurable (fun t : ℝ => u + t) := by fun_prop
  have hA : MeasurableSet (Set.Ioi u ∩ paymentTimes σ) :=
    measurableSet_Ioi.inter (paymentTimes_measurable σ)
  have hB : MeasurableSet
      (Set.Ioi (0 : ℝ) ∩
        ((fun t : ℝ => u + t) ⁻¹' paymentTimes σ)) :=
    measurableSet_Ioi.inter ((paymentTimes_measurable σ).preimage hshift)
  have hwindow (t : ℝ) :
      u + t ∈ Set.Ioi u ∩ paymentTimes σ ↔
        t ∈ Set.Ioi (0 : ℝ) ∩
          ((fun t : ℝ => u + t) ⁻¹' paymentTimes σ) := by
    simp only [Set.mem_inter_iff, Set.mem_Ioi, Set.mem_preimage]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨by linarith, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨by linarith, h2⟩
  exact lintegral_killed_discount_translation_of_measure_map
    μ ν u q (Set.Ioi u ∩ paymentTimes σ)
    (Set.Ioi (0 : ℝ) ∩ ((fun t : ℝ => u + t) ⁻¹' paymentTimes σ))
    hA hB hμ hwindow