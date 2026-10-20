-- Prove2me | solution 1 for AvramDividend.Classical.positiveLaplace_esscher_discounted_tail_kernel
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T16:34:08.335808+00:00
-- url     : https://prove2.me/submissions/5c8a437b-480a-4fac-9c12-047981289743

import Theorems.Thm_AvramDividend_Classical_positive_laplace_tail_withDensity
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Tactic.FunProp

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal


theorem solution
    (μ : Measure ℝ≥0) (φ s : ℝ) (hs : 0 < s) :
    let μφ : Measure ℝ≥0 :=
      μ.withDensity (fun z : ℝ≥0 =>
        ENNReal.ofReal (Real.exp (-(φ * (z : ℝ)))))
    let κφ : Measure ℝ :=
      (volume.restrict (Ioi (0 : ℝ))).withDensity
        (fun t : ℝ => μφ {z : ℝ≥0 | t < (z : ℝ)})
    (∫⁻ x : ℝ,
      ENNReal.ofReal (Real.exp (-(s * x))) ∂κφ) =
    ∫⁻ z : ℝ≥0,
      ENNReal.ofReal (Real.exp (-(φ * (z : ℝ)))) *
        ENNReal.ofReal ((1 - Real.exp (-(s * (z : ℝ)))) / s) ∂μ := by
  dsimp
  have htail :=
    positive_laplace_tail_withDensity
      (μ.withDensity (fun z : ℝ≥0 =>
        ENNReal.ofReal (Real.exp (-(φ * (z : ℝ)))))) s hs
  simp only [neg_mul] at htail
  rw [htail]
  have hf : Measurable (fun z : ℝ≥0 =>
      ENNReal.ofReal (Real.exp (-(φ * (z : ℝ))))) := by
    fun_prop
  have hg : Measurable (fun z : ℝ≥0 =>
      ENNReal.ofReal ((1 - Real.exp (-(s * (z : ℝ)))) / s)) := by
    fun_prop
  simpa only [Pi.mul_apply] using
    (lintegral_withDensity_eq_lintegral_mul μ hf hg)
