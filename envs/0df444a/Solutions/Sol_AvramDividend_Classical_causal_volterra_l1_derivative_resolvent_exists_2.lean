-- Prove2me | solution 2 for AvramDividend.Classical.causal_volterra_l1_derivative_resolvent_exists
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T20:58:57.361005+00:00
-- url     : https://prove2.me/submissions/07c2666d-008e-45f2-ab02-d41aa68a8dca

import Mathlib.MeasureTheory.Integral.IntegrableOn
import Theorems.Thm_AvramDividend_Classical_causal_volterra_exponential_kernel_weight_small
import Theorems.Thm_AvramDividend_Classical_causal_volterra_weighted_contraction_resolvent
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    (K : ℝ → ℝ) (a β : ℝ)
    (ha : 0 < a)
    (hK : IntegrableOn K (Ioi (0 : ℝ)) volume) :
    ∃ g : ℝ → ℝ,
      ContinuousOn g (Ici (0 : ℝ)) ∧
      (∀ x : ℝ, 0 < x →
        a * g x +
          (∫ s in Ioc (0 : ℝ) x,
            (β + K (x - s)) * g s ∂volume) = 1) := by
  obtain ⟨weight, hweight, hsmall⟩ :=
    causal_volterra_exponential_kernel_weight_small K a β ha hK
  exact causal_volterra_weighted_contraction_resolvent
    K a β weight ha hweight hK hsmall
