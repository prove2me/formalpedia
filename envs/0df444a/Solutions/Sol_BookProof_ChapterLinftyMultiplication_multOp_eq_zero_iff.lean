-- Prove2me | solution 1 for BookProof.ChapterLinftyMultiplication.multOp_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T15:38:12.543982+00:00
-- url     : https://prove2.me/submissions/3e845aa6-3108-4197-a805-cf8d5e4953dd

-- Generated from ChapterLinftyMultiplication.lean — solution of BookProof.ChapterLinftyMultiplication.multOp_eq_zero_iff
import Mathlib
import Definitions.Def_ChapterLinftyMultiplication
import Theorems.Thm_BookProof_ChapterLinftyMultiplication_multOp_coeFn
open BookProof.ChapterLinftyMultiplication



noncomputable section

open MeasureTheory ENNReal Complex


variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

set_option maxHeartbeats 1000000 in
theorem solution [IsFiniteMeasure μ] (φ : α → ℂ) (hφ : MemLp φ ⊤ μ) :
    multOp φ hφ = 0 ↔ φ =ᵐ[μ] 0 := by

  constructor
  · intro h
    set f : Lp ℂ 2 μ := (memLp_const (1 : ℂ)).toLp _ with hfdef
    have hf1 : (f : α → ℂ) =ᵐ[μ] fun _ => (1 : ℂ) := MemLp.coeFn_toLp _
    have h0 : (multOp φ hφ f : α → ℂ) =ᵐ[μ] 0 := by
      rw [h]
      simpa using Lp.coeFn_zero ℂ 2 μ
    filter_upwards [multOp_coeFn φ hφ f, hf1, h0] with x h1 h2 h3
    have : φ x * (f : α → ℂ) x = 0 := by rw [← h1]; simpa using h3
    rw [h2] at this
    simpa using this
  · intro h
    refine ContinuousLinearMap.ext fun f => Lp.ext ?_
    filter_upwards [multOp_coeFn φ hφ f, h, Lp.coeFn_zero ℂ 2 μ] with x h1 h2 h3
    simp only [ContinuousLinearMap.zero_apply]
    rw [h1, h3]
    simp at h2
    simp [h2]
