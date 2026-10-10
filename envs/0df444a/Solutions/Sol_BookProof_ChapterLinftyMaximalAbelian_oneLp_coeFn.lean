-- Prove2me | solution 1 for BookProof.ChapterLinftyMaximalAbelian.oneLp_coeFn
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T15:34:09.010564+00:00
-- url     : https://prove2.me/submissions/c6998771-f12c-4b10-b2d3-b6fa5195a8b2

-- Generated from ChapterLinftyMaximalAbelian.lean — solution of BookProof.ChapterLinftyMaximalAbelian.oneLp_coeFn
import Mathlib
import Definitions.Def_ChapterLinftyMaximalAbelian
import Definitions.Def_ChapterLinftyMultiplication
open BookProof.ChapterLinftyMaximalAbelian



noncomputable section

open MeasureTheory ENNReal Complex


open BookProof.ChapterLinftyMultiplication

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]

set_option maxHeartbeats 1000000 in
theorem solution : (oneLp μ : α → ℂ) =ᵐ[μ] fun _ => (1 : ℂ) := MemLp.coeFn_toLp _
