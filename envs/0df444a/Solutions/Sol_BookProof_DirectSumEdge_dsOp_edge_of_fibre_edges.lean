-- Prove2me | solution 1 for BookProof.DirectSumEdge.dsOp_edge_of_fibre_edges
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T05:48:26.874032+00:00
-- url     : https://prove2.me/submissions/59034376-522c-43d9-a503-53e352637307

-- Generated from ChapterDirectSumEdge.lean — solution of BookProof.DirectSumEdge.dsOp_edge_of_fibre_edges
import Mathlib
import Definitions.Def_ChapterDirectSumEdge
import Theorems.Thm_BookProof_DirectSumEdge_norm_sq_dsCore_eq_sum
import Theorems.Thm_BookProof_DirectSumEdge_quadForm_dsOp_eq_sum
open BookProof.DirectSumEdge




open BookProof.FarisLavine BookProof.DirectSumEsa

noncomputable section

variable {ι : Type*} {G : ι → Type*} [∀ i, NormedAddCommGroup (G i)]
  [∀ i, InnerProductSpace ℂ (G i)] {D : ∀ i, Submodule ℂ (G i)}

variable {ι : Type*} {G : ι → Type*} [∀ i, NormedAddCommGroup (G i)]
  [∀ i, InnerProductSpace ℂ (G i)] {D : ∀ i, Submodule ℂ (G i)}

set_option maxHeartbeats 1000000 in
theorem solution (H : ∀ i, D i →ₗ[ℂ] G i) (nu : ℝ)
    (hedge : ∀ i (u : D i), nu * ‖(u : G i)‖ ^ 2 ≤ quadForm (H i) u) (x : dsCore D) :
    nu * ‖(x : lp G 2)‖ ^ 2 ≤ quadForm (dsOp H) x := by

  rw [quadForm_dsOp_eq_sum H x, norm_sq_dsCore_eq_sum x, Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ =>
    hedge i ⟨((x : lp G 2) : ∀ i, G i) i, x.2.2 i⟩
