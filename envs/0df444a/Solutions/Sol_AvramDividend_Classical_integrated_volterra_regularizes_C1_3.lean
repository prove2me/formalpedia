-- Prove2me | solution 3 for AvramDividend.Classical.integrated_volterra_regularizes_C1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T22:41:17.960514+00:00
-- url     : https://prove2.me/submissions/c192e049-8707-44f0-a42d-25309f7364a5

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Theorems.Thm_AvramDividend_Classical_causal_volterra_l1_C1_solution_exists
import Theorems.Thm_AvramDividend_Classical_causal_volterra_l1_continuous_solution_unique
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    (V K : ℝ → ℝ) (a β : ℝ)
    (ha : 0 < a)
    (hK : IntegrableOn K (Ioi (0 : ℝ)) volume)
    (hVcont : ContinuousOn V (Ioi (0 : ℝ)))
    (hVbound : ∀ R : ℝ, 0 < R →
      ∃ C : ℝ, ∀ x : ℝ, x ∈ Ioc (0 : ℝ) R → |V x| ≤ C)
    (hEq : ∀ x : ℝ, 0 < x →
      a * V x +
        (∫ s in Ioc (0 : ℝ) x,
          (β + K (x - s)) * V s ∂volume) = x) :
    ContDiffOn ℝ 1 V (Ioi (0 : ℝ)) := by
  obtain ⟨G, hGc1, hGbound, hGeq⟩ :=
    causal_volterra_l1_C1_solution_exists K a β ha hK
  have hGcont : ContinuousOn G (Ioi (0 : ℝ)) :=
    hGc1.continuousOn
  have hVG : ∀ x : ℝ, 0 < x → V x = G x :=
    causal_volterra_l1_continuous_solution_unique
      K a β ha hK V G hVcont hGcont hVbound hGbound hEq hGeq
  exact hGc1.congr (by
    intro x hx
    exact hVG x hx)
