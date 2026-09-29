-- Prove2me | solution 1 for BookProof.FarisLavine.norm_sub_smul_sq
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-13T12:43:23.848534+00:00
-- url     : https://prove2.me/submissions/37ee3524-a24d-401b-b707-44ade03ac7d4

-- Generated from ChapterFarisLavineCore.lean — solution of BookProof.FarisLavine.norm_sub_smul_sq
import Mathlib
import Definitions.Def_ChapterFarisLavineCore
import Theorems.Thm_BookProof_FarisLavine_inner_apply_self_im
open BookProof.FarisLavine













variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D : Submodule ℂ F}

set_option maxHeartbeats 1000000 in
theorem solution (H : D →ₗ[ℂ] F) (hH : SymmetricOn D H) (d : ℝ) (x : D) :
    ‖H x - ((d : ℂ) * Complex.I) • (x : F)‖ ^ 2 = ‖H x‖ ^ 2 + d ^ 2 * ‖(x : F)‖ ^ 2 := by

  rw [norm_sub_sq (𝕜 := ℂ)]
  have h1 : (inner ℂ (H x) (((d : ℂ) * Complex.I) • (x : F)) : ℂ)
      = ((d : ℂ) * Complex.I) * inner ℂ (H x) (x : F) := inner_smul_right _ _ _
  have h2 : RCLike.re (inner ℂ (H x) (((d : ℂ) * Complex.I) • (x : F)) : ℂ) = 0 := by
    rw [h1]; simp [inner_apply_self_im H hH x]
  have h3 : ‖((d : ℂ) * Complex.I) • (x : F)‖ ^ 2 = d ^ 2 * ‖(x : F)‖ ^ 2 := by
    rw [norm_smul]; simp [mul_pow, sq_abs]
  rw [h2, h3]; ring
