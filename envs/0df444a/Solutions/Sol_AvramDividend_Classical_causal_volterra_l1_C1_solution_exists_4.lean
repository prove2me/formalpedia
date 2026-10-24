-- Prove2me | solution 4 for AvramDividend.Classical.causal_volterra_l1_C1_solution_exists
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T08:05:28.152317+00:00
-- url     : https://prove2.me/submissions/155b77ff-07cd-4545-8f4e-4312b338cfe7

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Theorems.Thm_AvramDividend_Classical_causal_volterra_l1_derivative_resolvent_exists
import Theorems.Thm_AvramDividend_Classical_causal_volterra_primitive_from_derivative_resolvent
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- A derivative resolvent has a C1 primitive solving the target equation. -/
theorem solution
    (K : ℝ → ℝ) (a β : ℝ)
    (ha : 0 < a)
    (hK : IntegrableOn K (Ioi (0 : ℝ)) volume) :
    ∃ G : ℝ → ℝ,
      ContDiffOn ℝ 1 G (Ioi (0 : ℝ)) ∧
      (∀ R : ℝ, 0 < R →
        ∃ C : ℝ, ∀ x : ℝ, x ∈ Ioc (0 : ℝ) R → |G x| ≤ C) ∧
      (∀ x : ℝ, 0 < x →
        a * G x +
          (∫ s in Ioc (0 : ℝ) x,
            (β + K (x - s)) * G s ∂volume) = x) := by
  obtain ⟨g, hg, hEq⟩ :=
    causal_volterra_l1_derivative_resolvent_exists K a β ha hK
  exact causal_volterra_primitive_from_derivative_resolvent
    K g a β ha hK hg hEq
