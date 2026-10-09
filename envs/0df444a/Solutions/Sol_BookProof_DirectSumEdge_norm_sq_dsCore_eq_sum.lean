-- Prove2me | solution 1 for BookProof.DirectSumEdge.norm_sq_dsCore_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T05:46:23.347413+00:00
-- url     : https://prove2.me/submissions/adca34a4-764c-4994-ad6d-938fb7db1860

-- Generated from ChapterDirectSumEdge.lean — solution of BookProof.DirectSumEdge.norm_sq_dsCore_eq_sum
import Mathlib
import Definitions.Def_ChapterDirectSumEdge
import Theorems.Thm_BookProof_DirectSumEdge_inner_dsCore_eq_sum
open BookProof.DirectSumEdge




open BookProof.FarisLavine BookProof.DirectSumEsa

noncomputable section

variable {ι : Type*} {G : ι → Type*} [∀ i, NormedAddCommGroup (G i)]
  [∀ i, InnerProductSpace ℂ (G i)] {D : ∀ i, Submodule ℂ (G i)}

variable {ι : Type*} {G : ι → Type*} [∀ i, NormedAddCommGroup (G i)]
  [∀ i, InnerProductSpace ℂ (G i)] {D : ∀ i, Submodule ℂ (G i)}

set_option maxHeartbeats 1000000 in
theorem solution (x : dsCore D) :
    ‖(x : lp G 2)‖ ^ 2 = ∑ i ∈ supportFinset x, ‖((x : lp G 2) : ∀ i, G i) i‖ ^ 2 := by

  have h := inner_dsCore_eq_sum x (x : lp G 2)
  have h' := congrArg Complex.re h
  rw [Complex.re_sum] at h'
  have hleft : (inner ℂ (x : lp G 2) (x : lp G 2) : ℂ).re = ‖(x : lp G 2)‖ ^ 2 :=
    inner_self_eq_norm_sq (𝕜 := ℂ) _
  rw [hleft] at h'
  refine h'.trans (Finset.sum_congr rfl fun i _ => ?_)
  exact inner_self_eq_norm_sq (𝕜 := ℂ) _
