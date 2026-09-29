-- Prove2me | solution 1 for BookProof.FarisLavine.quadForm_im
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-13T12:43:24.572831+00:00
-- url     : https://prove2.me/submissions/125f0a81-b9e0-424b-87c1-ad5be9c3dee3

-- Generated from ChapterFarisLavineCore.lean — solution of BookProof.FarisLavine.quadForm_im
import Mathlib
import Definitions.Def_ChapterFarisLavineCore
import Theorems.Thm_BookProof_FarisLavine_inner_im_swap
import Theorems.Thm_BookProof_FarisLavine_inner_apply_self_im
open BookProof.FarisLavine













variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D : Submodule ℂ F}

set_option maxHeartbeats 1000000 in
theorem solution (N : D →ₗ[ℂ] F) (hN : SymmetricOn D N) (x : D) :
    (inner ℂ (x : F) (N x) : ℂ).im = 0 := by

  rw [inner_im_swap (N x) (x : F), inner_apply_self_im N hN x, neg_zero]
