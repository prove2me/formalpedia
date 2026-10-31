-- Prove2me | solution 1 for BookProof.ChapterSolovaySeparableExistence.exists_separable_prob_with_arbitrary_finite_law
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-30T22:49:22.536889+00:00
-- url     : https://prove2.me/submissions/6e9eeaf5-9db1-4959-9323-dcef9fe2aefe

-- Generated from ChapterSolovaySeparableExistence.lean — solution of BookProof.ChapterSolovaySeparableExistence.exists_separable_prob_with_arbitrary_finite_law
import Mathlib
import Definitions.Def_ChapterSolovaySeparableExistence
import Theorems.Thm_BookProof_ChapterSolovaySeparableExistence_coordinateSpace_separable
import Definitions.Def_ChapterSolovayCoordinates
open BookProof.ChapterSolovaySeparableExistence



noncomputable section

open MeasureTheory ProbabilityTheory


open BookProof.ChapterSolovayCoordinates

set_option maxHeartbeats 1000000 in
theorem solution (N : ℕ)
    (headDist : Measure (Fin N → ℝ)) [IsProbabilityMeasure headDist] :
    TopologicalSpace.SeparableSpace (CoordinateSpace N) ∧
      ∃ μ : Measure (CoordinateSpace N), IsProbabilityMeasure μ ∧
        Measure.map Prod.fst μ = headDist ∧
        Measure.map Prod.snd μ = coordinateTailMeasure := by

  refine ⟨coordinateSpace_separable N, coordinateStateMeasure N headDist, inferInstance, ?_, ?_⟩
  · rw [coordinateStateMeasure, Measure.map_fst_prod, measure_univ, one_smul]
  · rw [coordinateStateMeasure, Measure.map_snd_prod, measure_univ, one_smul]
