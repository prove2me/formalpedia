-- Prove2me | solution 2 for AvramDividend.Classical.integrated_volterra_regularizes_C1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T21:01:20.077623+00:00
-- url     : https://prove2.me/submissions/cf14b28e-7042-4a22-a597-46d00089b797
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Theorems.Thm_AvramDividend_Classical_causal_volterra_l1_C1_solution_exists
import Theorems.Thm_AvramDividend_Classical_causal_volterra_l1_continuous_solution_unique

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Uniqueness transfers C1 regularity from an existing Volterra resolvent. -/
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
  obtain ⟨G, hGc, hGb, hGe⟩ :=
    causal_volterra_l1_C1_solution_exists K a β ha hK
  have hUnique : ∀ x : ℝ, 0 < x → V x = G x :=
    causal_volterra_l1_continuous_solution_unique
      K a β ha hK V G hVcont hGc.continuousOn
      hVbound hGb hEq hGe
  apply hGc.congr
  intro x hx
  exact hUnique x hx
