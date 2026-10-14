-- Prove2me | solution 1 for BookProof.ChapterWignerSymmetry.eq_norm_of_re_eq_norm
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T11:54:37.544706+00:00
-- url     : https://prove2.me/submissions/4b094a34-df4a-4de2-9e77-c2724771b2be

-- Generated from ChapterWignerSymmetry.lean — solution of BookProof.ChapterWignerSymmetry.eq_norm_of_re_eq_norm
import Mathlib
import Definitions.Def_ChapterWignerSymmetry
open BookProof.ChapterWignerSymmetry



open scoped InnerProductSpace ComplexConjugate
open Finset


variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]


variable {T : E → E}

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable {T : E → E}

set_option maxHeartbeats 1000000 in
theorem solution {z : ℂ} (h : z.re = ‖z‖) : z = (‖z‖ : ℂ) := by

  have hre : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by rw [Complex.sq_norm, Complex.normSq_apply]; ring
  rw [← h] at hre
  have h2 : z.im = 0 := by nlinarith [sq_nonneg z.im]
  apply Complex.ext <;> simp [h, h2]
