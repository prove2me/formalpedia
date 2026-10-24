-- Prove2me | solution 3 for AvramDividend.Classical.causal_volterra_l1_C1_solution_exists
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T22:01:39.267585+00:00
-- url     : https://prove2.me/submissions/b5b23584-0382-4773-911d-23b812286598

import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Theorems.Thm_AvramDividend_Classical_causal_volterra_l1_derivative_resolvent_exists
import Theorems.Thm_AvramDividend_Classical_causal_volterra_primitive_from_derivative_resolvent

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Existence of a C1 Volterra solution reduces to its derivative resolvent. -/
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
  obtain ⟨g, hgcont, hgeq⟩ :=
    causal_volterra_l1_derivative_resolvent_exists K a β ha hK
  exact causal_volterra_primitive_from_derivative_resolvent
    K g a β ha hK hgcont hgeq
