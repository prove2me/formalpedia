-- Prove2me | solution 1 for BookProof.ChapterLinftyMultiplication.multOp_inner_adjoint
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T15:38:01.173631+00:00
-- url     : https://prove2.me/submissions/0a3a6194-11e2-4971-8075-f72bf375bf1d

-- Generated from ChapterLinftyMultiplication.lean — solution of BookProof.ChapterLinftyMultiplication.multOp_inner_adjoint
import Mathlib
import Definitions.Def_ChapterLinftyMultiplication
import Theorems.Thm_BookProof_ChapterLinftyMultiplication_multOp_coeFn
import Theorems.Thm_BookProof_ChapterLinftyMultiplication_memLp_top_conj
open BookProof.ChapterLinftyMultiplication



noncomputable section

open MeasureTheory ENNReal Complex


variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

set_option maxHeartbeats 1000000 in
theorem solution (φ : α → ℂ) (hφ : MemLp φ ⊤ μ) (f g : Lp ℂ 2 μ) :
    inner ℂ (multOp φ hφ f) g
      = inner ℂ f (multOp (fun x => (starRingEnd ℂ) (φ x)) (memLp_top_conj hφ) g) := by

  rw [L2.inner_def, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [multOp_coeFn φ hφ f,
    multOp_coeFn (fun x => (starRingEnd ℂ) (φ x)) (memLp_top_conj hφ) g] with x h1 h2
  simp only [h1, h2, RCLike.inner_apply, map_mul]
  ring
