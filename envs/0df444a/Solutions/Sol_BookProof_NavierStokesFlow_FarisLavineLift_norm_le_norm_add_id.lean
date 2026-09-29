-- Prove2me | solution 1 for BookProof.NavierStokesFlow.FarisLavineLift.norm_le_norm_add_id
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T07:37:30.476028+00:00
-- url     : https://prove2.me/submissions/4cb4c4b4-183a-4d6b-8f8b-6a0e39a8115c

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.Linarith
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {D : Submodule ℂ F}

theorem solution (N : D →ₗ[ℂ] D) (v : D)
    (hpos : 0 ≤ (inner ℂ ((N v : D) : F) ((v : F)) : ℂ).re) :
    ‖((N v : D) : F)‖ ≤ ‖((((N + LinearMap.id : D →ₗ[ℂ] D)) v : D) : F)‖ := by
  change ‖((N v : D) : F)‖ ≤ ‖((N v : D) : F) + (v : F)‖
  have hsq := norm_add_sq (𝕜 := ℂ) ((N v : D) : F) (v : F)
  change ‖((N v : D) : F) + (v : F)‖ ^ 2 = ‖((N v : D) : F)‖ ^ 2 + 2 * (inner ℂ ((N v : D) : F) (v : F)).re + ‖(v : F)‖ ^ 2 at hsq
  nlinarith [norm_nonneg ((N v : D) : F), norm_nonneg (((N v : D) : F) + (v : F)), sq_nonneg ‖(v : F)‖]
#print axioms solution
