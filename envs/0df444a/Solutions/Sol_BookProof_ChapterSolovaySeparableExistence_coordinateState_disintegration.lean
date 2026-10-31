-- Prove2me | solution 1 for BookProof.ChapterSolovaySeparableExistence.coordinateState_disintegration
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-30T22:49:48.821009+00:00
-- url     : https://prove2.me/submissions/92be2fa9-4bf6-424a-863f-9b346357856d

-- Generated from ChapterSolovaySeparableExistence.lean — solution of BookProof.ChapterSolovaySeparableExistence.coordinateState_disintegration
import Mathlib
import Definitions.Def_ChapterSolovaySeparableExistence
import Theorems.Thm_BookProof_ChapterSolovaySeparableExistence_prod_disintegration
import Definitions.Def_ChapterSolovayCoordinates
open BookProof.ChapterSolovaySeparableExistence



noncomputable section

open MeasureTheory ProbabilityTheory


open BookProof.ChapterSolovayCoordinates

set_option maxHeartbeats 1000000 in
theorem solution (N : ℕ) (μ : Measure (CoordinateSpace N))
    [IsFiniteMeasure μ] :
    ∃ κ : Kernel (Fin N → ℝ) CoordinateTail, IsMarkovKernel κ ∧ μ.fst ⊗ₘ κ = μ := prod_disintegration μ
