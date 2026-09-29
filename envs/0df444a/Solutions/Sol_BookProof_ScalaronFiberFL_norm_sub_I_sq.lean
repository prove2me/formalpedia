-- Prove2me | solution 1 for BookProof.ScalaronFiberFL.norm_sub_I_sq
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-17T19:45:43.085353+00:00
-- url     : https://prove2.me/submissions/d1cee86e-c4df-4665-9321-9389ac9ba557

-- Generated from ChapterScalaronFiberFL.lean — solution of BookProof.ScalaronFiberFL.norm_sub_I_sq
import Mathlib
import Definitions.Def_ChapterQgOuterFockFarisLavine
import Definitions.Def_ChapterFarisLavineCore
import Theorems.Thm_BookProof_FarisLavine_inner_apply_self_im
open BookProof.FarisLavine

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
variable {D : Submodule ℂ F}

set_option maxHeartbeats 1000000 in
theorem solution (N : D →ₗ[ℂ] F) (hsym : SymmetricOn D N) (u : D) :
    ‖N u - Complex.I • (u : F)‖ ^ 2 = ‖N u‖ ^ 2 + ‖(u : F)‖ ^ 2 := by
  have him : (inner ℂ (N u) (u : F) : ℂ).im = 0 := inner_apply_self_im N hsym u
  have hre : (inner ℂ (N u) (Complex.I • (u : F)) : ℂ).re = 0 := by
    rw [inner_smul_right, Complex.mul_re, him]
    simp
  have hnorm : ‖Complex.I • (u : F)‖ = ‖(u : F)‖ := by
    rw [norm_smul]; simp
  rw [norm_sub_sq (𝕜 := ℂ), hnorm]
  simp only [RCLike.re_to_complex] at hre ⊢
  rw [hre]
  ring
