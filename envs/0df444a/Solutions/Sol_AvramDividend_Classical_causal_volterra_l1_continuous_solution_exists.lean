-- Prove2me | solution 1 for AvramDividend.Classical.causal_volterra_l1_continuous_solution_exists
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T22:07:10.407416+00:00
-- url     : https://prove2.me/submissions/de43f751-870c-43e7-86c0-86c7de2bd084
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Theorems.Thm_AvramDividend_Classical_causal_volterra_l1_derivative_resolvent_exists
import Theorems.Thm_AvramDividend_Classical_causal_volterra_primitive_from_derivative_resolvent

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    (K : ℝ → ℝ) (a β : ℝ)
    (ha : 0 < a)
    (hK : IntegrableOn K (Ioi (0 : ℝ)) volume) :
    ∃ G : ℝ → ℝ,
      ContinuousOn G (Ioi (0 : ℝ)) ∧
      (∀ R : ℝ, 0 < R →
        ∃ C : ℝ, ∀ x : ℝ, x ∈ Ioc (0 : ℝ) R → |G x| ≤ C) ∧
      (∀ x : ℝ, 0 < x →
        a * G x +
          (∫ s in Ioc (0 : ℝ) x,
            (β + K (x - s)) * G s ∂volume) = x) := by
  obtain ⟨g, hgcont, hgeq⟩ :=
    causal_volterra_l1_derivative_resolvent_exists K a β ha hK
  obtain ⟨G, hGc, hGb, hGe⟩ :=
    causal_volterra_primitive_from_derivative_resolvent K g a β ha hK hgcont hgeq
  exact ⟨G, hGc.continuousOn, hGb, hGe⟩
