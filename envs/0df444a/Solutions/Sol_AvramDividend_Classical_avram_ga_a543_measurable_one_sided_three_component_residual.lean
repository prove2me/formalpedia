-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a543_measurable_one_sided_three_component_residual
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T07:43:08.511741+00:00
-- url     : https://prove2.me/submissions/37ff1af1-5b5f-452d-9836-0284082e2960

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ga_a533_one_sided_three_source_integrability
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
noncomputable section

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (W A B C : Ω → ℝ)
    (hAmeas : AEStronglyMeasurable A P)
    (hA : Integrable (fun ω => max (A ω) (0 : ℝ)) P)
    (hB : Integrable B P) (hC : Integrable C P)
    (hEq : ∀ ω, W ω = A ω - B ω - C ω) :
    AEStronglyMeasurable W P ∧
      Integrable (fun ω => max (W ω) (0 : ℝ)) P := by
  have hABC : AEStronglyMeasurable
      (fun ω => A ω - B ω - C ω) P :=
    (hAmeas.sub hB.aestronglyMeasurable).sub hC.aestronglyMeasurable
  have hW : AEStronglyMeasurable W P :=
    hABC.congr (Filter.Eventually.of_forall fun ω => (hEq ω).symm)
  have hMeas : AEStronglyMeasurable
      (fun ω => max (A ω - B ω - C ω) (0 : ℝ)) P :=
    (continuous_id.max continuous_const).comp_aestronglyMeasurable hABC
  have hI := avram_ga_a533_one_sided_three_source_integrability
    A B C hA hB hC hMeas
  refine ⟨hW, ?_⟩
  exact hI.congr (Filter.Eventually.of_forall fun ω =>
    congrArg (fun z : ℝ => max z 0) (hEq ω).symm)
