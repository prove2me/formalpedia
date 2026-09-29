-- Prove2me | solution 1 for BookProof.FarisLavine.inner_im_swap
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-12T23:48:41.557065+00:00
-- url     : https://prove2.me/submissions/bda27cac-c44a-4f30-92f1-ca4edcde9743

-- Generated from ChapterFarisLavineCore.lean — solution of BookProof.FarisLavine.inner_im_swap
import Mathlib
import Definitions.Def_ChapterFarisLavineCore
open BookProof.FarisLavine













variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D : Submodule ℂ F}

set_option maxHeartbeats 1000000 in
theorem solution (a b : F) : (inner ℂ b a : ℂ).im = -(inner ℂ a b : ℂ).im := by

  rw [← inner_conj_symm (𝕜 := ℂ) a b, Complex.conj_im, neg_neg]
