-- Prove2me | solution 1 for BookProof.ChapterSolovaySeparableExistence.prod_disintegration
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-30T22:49:44.967072+00:00
-- url     : https://prove2.me/submissions/a8f02dbe-1bec-4993-8848-2b52b2294929

-- Generated from ChapterSolovaySeparableExistence.lean — solution of BookProof.ChapterSolovaySeparableExistence.prod_disintegration
import Mathlib
import Definitions.Def_ChapterSolovaySeparableExistence
import Definitions.Def_ChapterSolovayCoordinates
open BookProof.ChapterSolovaySeparableExistence



noncomputable section

open MeasureTheory ProbabilityTheory


open BookProof.ChapterSolovayCoordinates

set_option maxHeartbeats 1000000 in
theorem solution {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [StandardBorelSpace Y] [Nonempty Y] (μ : Measure (X × Y)) [IsFiniteMeasure μ] :
    ∃ κ : Kernel X Y, IsMarkovKernel κ ∧ μ.fst ⊗ₘ κ = μ := ⟨μ.condKernel, inferInstance, Measure.disintegrate μ μ.condKernel⟩
