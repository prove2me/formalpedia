-- Prove2me | solution 1 for BookProof.ChapterSelectingEvents.exists_regular_conditional_probability
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T09:30:53.319105+00:00
-- url     : https://prove2.me/submissions/db2d6d6e-2010-462e-9689-915ef599c2ac

-- Generated from ChapterSelectingEvents.lean — solution of BookProof.ChapterSelectingEvents.exists_regular_conditional_probability
import Mathlib
import Definitions.Def_ChapterSelectingEvents
open BookProof.ChapterSelectingEvents



open scoped BigOperators
open MeasureTheory ProbabilityTheory


variable (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {Ω Data : Type*} [MeasurableSpace Ω]

set_option maxHeartbeats 1000000 in
theorem solution
    [StandardBorelSpace Ω] [Nonempty Ω] [MeasurableSpace Data]
    (μ : Measure Ω) [IsFiniteMeasure μ] (X : Ω → Data) :
    ∃ κ : Kernel Data Ω, IsMarkovKernel κ ∧
      (μ.map X) ⊗ₘ κ = μ.map (fun ω => (X ω, ω)) := ⟨condDistrib id X μ, inferInstance, compProd_map_condDistrib aemeasurable_id⟩
