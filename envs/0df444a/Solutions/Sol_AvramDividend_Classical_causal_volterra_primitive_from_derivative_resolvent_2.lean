-- Prove2me | solution 2 for AvramDividend.Classical.causal_volterra_primitive_from_derivative_resolvent
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T20:46:54.642005+00:00
-- url     : https://prove2.me/submissions/d7ac0dcf-f7b4-4e84-9d6b-fe81e509b9f4

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Theorems.Thm_AvramDividend_Classical_causal_primitive_C1_locally_bounded
import Theorems.Thm_AvramDividend_Classical_causal_volterra_integrated_identity_of_resolvent
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    (K g : ℝ → ℝ) (a β : ℝ)
    (ha : 0 < a)
    (hK : IntegrableOn K (Ioi (0 : ℝ)) volume)
    (hg : ContinuousOn g (Ici (0 : ℝ)))
    (hgeq : ∀ x : ℝ, 0 < x →
      a * g x +
        (∫ s in Ioc (0 : ℝ) x,
          (β + K (x - s)) * g s ∂volume) = 1) :
    ∃ G : ℝ → ℝ,
      ContDiffOn ℝ 1 G (Ioi (0 : ℝ)) ∧
      (∀ R : ℝ, 0 < R →
        ∃ C : ℝ, ∀ x : ℝ, x ∈ Ioc (0 : ℝ) R → |G x| ≤ C) ∧
      (∀ x : ℝ, 0 < x →
        a * G x +
          (∫ s in Ioc (0 : ℝ) x,
            (β + K (x - s)) * G s ∂volume) = x) := by
  let G : ℝ → ℝ := fun x => ∫ s in Ioc (0 : ℝ) x, g s ∂volume
  obtain ⟨hC1, hbound⟩ := causal_primitive_C1_locally_bounded g hg
  refine ⟨G, hC1, hbound, ?_⟩
  exact causal_volterra_integrated_identity_of_resolvent K g a β ha hK hg hgeq
