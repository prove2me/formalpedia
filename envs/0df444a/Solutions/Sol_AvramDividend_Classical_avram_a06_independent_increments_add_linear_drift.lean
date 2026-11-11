-- Prove2me | solution 1 for AvramDividend.Classical.avram_a06_independent_increments_add_linear_drift
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T00:51:13.416663+00:00
-- url     : https://prove2.me/submissions/01c87964-c8a4-4249-ba40-658872424038

import Mathlib.Probability.ConditionalProbability
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_LeanLevy_Processes_StochasticProcess
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Z : ℝ≥0 → Ω → ℝ) (b : ℝ)
    (hZ : HasIndependentIncrements Z P) :
    HasIndependentIncrements (fun t ω => Z t ω + b * (t : ℝ)) P := by
  intro n t ht
  have h := hZ n t ht
  have hcomp := h.comp
    (fun (i : Fin n) (z : ℝ) =>
      z + b * ((t i.succ : ℝ) - (t i.castSucc : ℝ)))
    (by intro i; fun_prop)
  convert hcomp using 1
  funext i ω
  simp only [ProbabilityTheory.increment, Function.comp_apply,
    Pi.sub_apply, Pi.add_apply]
  ring
