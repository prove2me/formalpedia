-- Prove2me | solution 1 for AvramDividend.Classical.avram_e0_natural_filtration_from_leanlevy_increment
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-08T00:40:21.3543+00:00
-- url     : https://prove2.me/submissions/9f54e01e-f059-4941-98ac-c8e48844ec0c

import Mathlib
import Definitions.Def_LeanLevy_Processes_StochasticProcess
import Theorems.Thm_ProbabilityTheory_stronglyAdapted_naturalFiltration
import Theorems.Thm_ProbabilityTheory_HasIndependentIncrements_indep_naturalFiltration
import Theorems.Thm_ProbabilityTheory_increment_apply

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
noncomputable section

/-- The accepted LeanLevy natural-filtration theorems supply both fields. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsZeroOrProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ)
    (hmeas : ∀ t : ℝ≥0, StronglyMeasurable (X t))
    (hzero : X 0 = fun _ => 0)
    (hindep : ProbabilityTheory.HasIndependentIncrements X P) :
    StronglyAdapted (Filtration.natural (fun t => X t) hmeas) X ∧
      ∀ s t : ℝ≥0, s ≤ t →
        ProbabilityTheory.Indep
          (MeasurableSpace.comap (fun ω => X t ω - X s ω) inferInstance)
          ((Filtration.natural (fun t => X t) hmeas).seq s) P := by
  constructor
  · exact ProbabilityTheory.stronglyAdapted_naturalFiltration hmeas
  · intro s t hst
    have hfun : ProbabilityTheory.increment X s t =
        (fun ω => X t ω - X s ω) := by
      funext ω
      exact ProbabilityTheory.increment_apply X s t ω
    rw [← hfun]
    exact ProbabilityTheory.HasIndependentIncrements.indep_naturalFiltration
      hindep hmeas hzero (fun i => bot_le) hst
