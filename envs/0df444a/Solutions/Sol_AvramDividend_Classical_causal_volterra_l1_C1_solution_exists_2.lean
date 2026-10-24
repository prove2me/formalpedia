-- Prove2me | solution 2 for AvramDividend.Classical.causal_volterra_l1_C1_solution_exists
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T21:05:40.655888+00:00
-- url     : https://prove2.me/submissions/4246078b-4391-4b2a-b55b-0649441b8800

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Theorems.Thm_AvramDividend_Classical_causal_volterra_l1_derivative_resolvent_exists
import Theorems.Thm_AvramDividend_Classical_causal_volterra_primitive_from_derivative_resolvent
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set

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
  obtain ⟨g, hg, hgeq⟩ :=
    causal_volterra_l1_derivative_resolvent_exists K a β ha hK
  exact causal_volterra_primitive_from_derivative_resolvent
    K g a β ha hK hg hgeq
