-- Prove2me | solution 4 for AvramDividend.Classical.causal_volterra_l1_derivative_resolvent_exists
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T08:09:30.307782+00:00
-- url     : https://prove2.me/submissions/2407321d-fff0-468a-b93a-de6345be97d5

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
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