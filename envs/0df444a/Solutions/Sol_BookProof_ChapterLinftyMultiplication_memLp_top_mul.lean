-- Prove2me | solution 1 for BookProof.ChapterLinftyMultiplication.memLp_top_mul
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-07T10:37:14.380319+00:00
-- url     : https://prove2.me/submissions/e11a4aa5-20aa-4cde-a862-82a38981b052

-- Generated from ChapterLinftyMultiplication.lean — solution of BookProof.ChapterLinftyMultiplication.memLp_top_mul
import Mathlib
import Definitions.Def_ChapterLinftyMultiplication
open BookProof.ChapterLinftyMultiplication



noncomputable section

open MeasureTheory ENNReal Complex


variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

set_option maxHeartbeats 1000000 in
theorem solution {φ ψ : α → ℂ} (hφ : MemLp φ ⊤ μ) (hψ : MemLp ψ ⊤ μ) :
    MemLp (fun x => φ x * ψ x) ⊤ μ := MemLp.smul (p := ⊤) (q := ⊤) (r := ⊤) hψ hφ
