-- Prove2me | solution 1 for BookProof.ChapterBornMeasure.norm_evolve
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T05:40:59.395778+00:00
-- url     : https://prove2.me/submissions/44adaee6-c65f-4605-833a-ada4d75ab681

-- Generated from ChapterBornMeasure.lean — solution of BookProof.ChapterBornMeasure.norm_evolve
import Mathlib
import Definitions.Def_ChapterBornMeasure
import Definitions.Def_ChapterContinuityUnitary
open BookProof.ChapterBornMeasure



open MeasureTheory
open scoped ENNReal


variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

set_option maxHeartbeats 1000000 in
theorem solution (H : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) (hH : IsSelfAdjoint H) (t : ℝ)
    (psi : Lp ℂ 2 μ) : ‖evolve H t psi‖ = ‖psi‖ :=
  BookProof.ChapterContinuityUnitaryInfinite.norm_of_unitary _
      (BookProof.ChapterContinuityUnitaryInfinite.exp_smul_I_unitary H hH t).1 psi
