-- Prove2me | solution 1 for AvramDividend.Classical.causal_volterra_l1_C1_solution_exists
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T16:19:32.042379+00:00
-- url     : https://prove2.me/submissions/54f745f7-f6a7-4d24-806b-486e8b1212d3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
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
      ContDiffOn ℝ 1 G (Ioi (0 : ℝ)) ∧
      (∀ R : ℝ, 0 < R →
        ∃ C : ℝ, ∀ x : ℝ, x ∈ Ioc (0 : ℝ) R → |G x| ≤ C) ∧
      (∀ x : ℝ, 0 < x →
        a * G x +
          (∫ s in Ioc (0 : ℝ) x,
            (β + K (x - s)) * G s ∂volume) = x) := by
  obtain ⟨g, hg, hgeq⟩ :=
    AvramDividend.Classical.causal_volterra_l1_derivative_resolvent_exists
      K a β ha hK
  exact AvramDividend.Classical.causal_volterra_primitive_from_derivative_resolvent
    K g a β ha hK hg hgeq
