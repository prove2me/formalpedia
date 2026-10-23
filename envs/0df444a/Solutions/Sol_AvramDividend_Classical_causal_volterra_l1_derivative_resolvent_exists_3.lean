-- Prove2me | solution 3 for AvramDividend.Classical.causal_volterra_l1_derivative_resolvent_exists
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T21:03:35.08788+00:00
-- url     : https://prove2.me/submissions/2cf453e5-bfe7-4970-a02d-f887f2a6538c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.MeasureTheory.Integral.IntegrableOn
import Theorems.Thm_AvramDividend_Classical_causal_volterra_exponential_kernel_weight_small
import Theorems.Thm_AvramDividend_Classical_causal_volterra_weighted_contraction_resolvent

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Choose a contraction weight and invoke the weighted resolvent theorem. -/
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
