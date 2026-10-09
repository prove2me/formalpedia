-- Prove2me | solution 1 for BookProof.DirectSumEdge.quadForm_dsOp_eq_sum
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T05:47:24.581985+00:00
-- url     : https://prove2.me/submissions/2520c69f-3b77-4f3e-8045-496dfe0e32bc
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterDirectSumEdge.lean — solution of BookProof.DirectSumEdge.quadForm_dsOp_eq_sum
import Mathlib
import Definitions.Def_ChapterDirectSumEdge
import Theorems.Thm_BookProof_DirectSumEdge_inner_dsOp_eq_sum
open BookProof.DirectSumEdge




open BookProof.FarisLavine BookProof.DirectSumEsa

noncomputable section

variable {ι : Type*} {G : ι → Type*} [∀ i, NormedAddCommGroup (G i)]
  [∀ i, InnerProductSpace ℂ (G i)] {D : ∀ i, Submodule ℂ (G i)}

variable {ι : Type*} {G : ι → Type*} [∀ i, NormedAddCommGroup (G i)]
  [∀ i, InnerProductSpace ℂ (G i)] {D : ∀ i, Submodule ℂ (G i)}

set_option maxHeartbeats 1000000 in
theorem solution (H : ∀ i, D i →ₗ[ℂ] G i) (x : dsCore D) :
    quadForm (dsOp H) x
      = ∑ i ∈ supportFinset x,
          quadForm (H i) ⟨((x : lp G 2) : ∀ i, G i) i, x.2.2 i⟩ := by

  unfold quadForm
  rw [inner_dsOp_eq_sum H x, Complex.re_sum]
