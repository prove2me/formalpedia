-- Prove2me | solution 1 for BookProof.ChapterSolovaySeparableExistence.exists_separable_prob_with_arbitrary_finite_law_substrate
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-30T22:49:40.908554+00:00
-- url     : https://prove2.me/submissions/83c49d14-39e2-4729-9615-8e5b4af115f3

-- Generated from ChapterSolovaySeparableExistence.lean — solution of BookProof.ChapterSolovaySeparableExistence.exists_separable_prob_with_arbitrary_finite_law_substrate
import Mathlib
import Definitions.Def_ChapterSolovaySeparableExistence
import Theorems.Thm_BookProof_ChapterSolovaySeparableExistence_innerSpace_separable
import Definitions.Def_ChapterSolovayCoordinates
import Definitions.Def_PhysMeasureBasis
open BookProof.ChapterSolovaySeparableExistence



noncomputable section

open MeasureTheory ProbabilityTheory


open BookProof.ChapterSolovayCoordinates
open PhysMeasureBasis

set_option maxHeartbeats 1000000 in
theorem solution (N : ℕ)
    (headDist : Measure (_root_.InnerHead N)) [IsProbabilityMeasure headDist] :
    TopologicalSpace.SeparableSpace (_root_.InnerSpace N) ∧
      ∃ μ : Measure (_root_.InnerSpace N), IsProbabilityMeasure μ ∧
        Measure.map Prod.fst μ = headDist ∧
        Measure.map Prod.snd μ = _root_.tailMeasure := by

  refine ⟨innerSpace_separable N, _root_.stateMeasure N headDist, inferInstance, ?_, ?_⟩
  · rw [_root_.stateMeasure, Measure.map_fst_prod, measure_univ, one_smul]
  · rw [_root_.stateMeasure, Measure.map_snd_prod, measure_univ, one_smul]
