-- Prove2me | solution 1 for AvramDividend.Classical.integrated_volterra_regularizes_C1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T11:04:42.924691+00:00
-- url     : https://prove2.me/submissions/5f97d47f-6a2c-4f91-a9b4-f5a41ca37e7e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Theorems.Thm_AvramDividend_Classical_causal_volterra_l1_C1_solution_exists
import Theorems.Thm_AvramDividend_Classical_causal_volterra_l1_continuous_solution_unique
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set

/-- Reduce C1 regularity to existence and uniqueness of the causal L1 Volterra resolvent. -/
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
  obtain ⟨G, hGdiff, hGbound, hGeq⟩ :=
    causal_volterra_l1_C1_solution_exists K a β ha hK
  have hGcont : ContinuousOn G (Ioi (0 : ℝ)) :=
    hGdiff.continuousOn
  have hident : ∀ x : ℝ, 0 < x → V x = G x :=
    causal_volterra_l1_continuous_solution_unique
      K a β ha hK V G hVcont hGcont hVbound hGbound hEq hGeq
  apply hGdiff.congr
  intro x hx
  exact hident x hx
