-- Prove2me | solution 1 for GambiniPullin.weightedModelIntegral_rotational_zero
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-25T12:54:08.327064+00:00
-- url     : https://prove2.me/submissions/85c74ba1-9524-4ce6-bad9-d1824aa939ef

import Mathlib
import Definitions.Def_GambiniPullin_AppendixA_Defs

set_option autoImplicit false

open MeasureTheory Filter GambiniPullin in
theorem solution (β : ℝ) (hβ : 0 < β) :
    weightedModelIntegral 0 β 0 = 0 := by
  unfold weightedModelIntegral
  have hodd : ∀ p : ℝ × ℝ,
      weightedModelIntegrand 0 β 0 p.2 p.1 = -weightedModelIntegrand 0 β 0 p.1 p.2 := by
    intro p
    simp only [weightedModelIntegrand, modelIntegrand, modelDenom, zero_mul, add_zero,
      div_one, neg_zero, Real.exp_zero, one_mul]
    rw [add_comm (p.2 ^ 2) (p.1 ^ 2)]
    have h : (1 : ℝ) + p.2 ^ 2 + p.1 ^ 2 = 1 + p.1 ^ 2 + p.2 ^ 2 := by ring
    rw [h]
    ring
  have key := integral_prod_swap (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
    (fun p : ℝ × ℝ => weightedModelIntegrand 0 β 0 p.1 p.2)
  simp only [Prod.fst_swap, Prod.snd_swap, hodd, integral_neg] at key
  rw [Measure.volume_eq_prod]
  linarith
