-- Prove2me | solution 1 for BookProof.ChapterLinftyMultiplication.multOp_coeFn
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T09:48:00.856856+00:00
-- url     : https://prove2.me/submissions/5fbf3569-013b-4737-97fc-4dfd858f5517

-- Generated from ChapterLinftyMultiplication.lean — solution of BookProof.ChapterLinftyMultiplication.multOp_coeFn
import Mathlib
import Definitions.Def_ChapterLinftyMultiplication
open BookProof.ChapterLinftyMultiplication



noncomputable section

open MeasureTheory ENNReal Complex


variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

set_option maxHeartbeats 1000000 in
theorem solution (φ : α → ℂ) (hφ : MemLp φ ⊤ μ) (f : Lp ℂ 2 μ) :
    (multOp φ hφ f : α → ℂ) =ᵐ[μ] fun x => φ x * (f : α → ℂ) x := MemLp.coeFn_toLp (mul_memLp_two hφ f)
