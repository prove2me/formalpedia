-- Prove2me | solution 1 for BookProof.ChapterTensorCompleteness.hasSum_tensorHilbertBasis
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-22T09:35:32.545287+00:00
-- url     : https://prove2.me/submissions/e17b9c13-6759-4069-9c98-ac4e54b59b18

-- Generated from ChapterTensorCompleteness.lean — solution of BookProof.ChapterTensorCompleteness.hasSum_tensorHilbertBasis
import Mathlib
import Definitions.Def_ChapterTensorCompleteness
import Theorems.Thm_BookProof_ChapterTensorCompleteness_tensorHilbertBasis_repr_apply
import Definitions.Def_ChapterSolovayHilbertTensor
open BookProof.ChapterTensorCompleteness



noncomputable section

open MeasureTheory ENNReal Complex Filter Topology


open BookProof.ChapterSolovayHilbertTensor

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
  {μ : Measure α} {ν : Measure β} [IsFiniteMeasure μ] [IsFiniteMeasure ν]

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
  {μ : Measure α} {ν : Measure β} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
variable {ι κ : Type*}

set_option maxHeartbeats 1000000 in
theorem solution
    (b : HilbertBasis ι ℂ (Lp ℂ 2 μ)) (c : HilbertBasis κ ℂ (Lp ℂ 2 ν))
    (F : Lp ℂ 2 (μ.prod ν)) :
    HasSum (fun p : ι × κ =>
        (inner ℂ (tensorOf (b p.1) (c p.2)) F : ℂ) • tensorOf (b p.1) (c p.2)) F := by

  have h := (tensorHilbertBasis b c).hasSum_repr F
  simpa only [tensorHilbertBasis_repr_apply, coe_tensorHilbertBasis] using h
