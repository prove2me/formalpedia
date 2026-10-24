-- Prove2me | solution 1 for AvramDividend.Classical.causal_volterra_l1_derivative_resolvent_exists
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T17:15:19.374633+00:00
-- url     : https://prove2.me/submissions/37b34586-e2fd-4b8e-8c65-f052c8679aec

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
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
  obtain ⟨w, hw, hsmall⟩ :=
    AvramDividend.Classical.causal_volterra_exponential_kernel_weight_small
      K a β ha hK
  exact AvramDividend.Classical.causal_volterra_weighted_contraction_resolvent
    K a β w ha hw hK hsmall
