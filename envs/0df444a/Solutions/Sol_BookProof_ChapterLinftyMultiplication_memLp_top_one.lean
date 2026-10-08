-- Prove2me | solution 1 for BookProof.ChapterLinftyMultiplication.memLp_top_one
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-07T10:37:16.188989+00:00
-- url     : https://prove2.me/submissions/6cef3a42-8f0d-433f-9ca7-bd130680678f

-- Generated from ChapterLinftyMultiplication.lean — solution of BookProof.ChapterLinftyMultiplication.memLp_top_one
import Mathlib
import Definitions.Def_ChapterLinftyMultiplication
open BookProof.ChapterLinftyMultiplication



noncomputable section

open MeasureTheory ENNReal Complex


variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

set_option maxHeartbeats 1000000 in
theorem solution : MemLp (fun _ : α => (1 : ℂ)) ⊤ μ := memLp_top_const 1
