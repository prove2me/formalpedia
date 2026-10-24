-- Prove2me | solution 4 for AvramDividend.Classical.integrated_volterra_regularizes_C1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T08:27:20.338225+00:00
-- url     : https://prove2.me/submissions/8cbc8ee6-d3b4-4a4f-a7c4-0bf522e751df

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Theorems.Thm_AvramDividend_Classical_causal_volterra_l1_C1_solution_exists
import Theorems.Thm_AvramDividend_Classical_causal_volterra_l1_continuous_solution_unique

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Every continuous locally bounded solution inherits C1 regularity from the unique resolvent. -/
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
  obtain ⟨G, hGdiff, hGbound, hGsol⟩ :=
    causal_volterra_l1_C1_solution_exists K a β ha hK
  have hGc : ContinuousOn G (Ioi (0 : ℝ)) := hGdiff.continuousOn
  have hEqVG : ∀ x ∈ Ioi (0 : ℝ), V x = G x := by
    intro x hx
    exact causal_volterra_l1_continuous_solution_unique
      K a β ha hK V G hVcont hGc hVbound hGbound hEq hGsol x hx
  exact hGdiff.congr hEqVG
