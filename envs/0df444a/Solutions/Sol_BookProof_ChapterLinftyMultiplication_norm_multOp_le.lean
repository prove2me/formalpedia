-- Prove2me | solution 1 for BookProof.ChapterLinftyMultiplication.norm_multOp_le
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T15:36:54.173204+00:00
-- url     : https://prove2.me/submissions/aa7bcb06-4785-4a68-ada5-ff1c4b404ff4

-- Generated from ChapterLinftyMultiplication.lean — solution of BookProof.ChapterLinftyMultiplication.norm_multOp_le
import Mathlib
import Definitions.Def_ChapterLinftyMultiplication
open BookProof.ChapterLinftyMultiplication



noncomputable section

open MeasureTheory ENNReal Complex


variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

set_option maxHeartbeats 1000000 in
theorem solution (φ : α → ℂ) (hφ : MemLp φ ⊤ μ) :
    ‖multOp φ hφ‖ ≤ (eLpNorm φ ⊤ μ).toReal := LinearMap.mkContinuous_norm_le _ ENNReal.toReal_nonneg _
