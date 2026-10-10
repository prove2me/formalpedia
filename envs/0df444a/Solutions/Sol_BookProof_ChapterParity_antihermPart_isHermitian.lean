-- Prove2me | solution 1 for BookProof.ChapterParity.antihermPart_isHermitian
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T09:12:29.246962+00:00
-- url     : https://prove2.me/submissions/371d5992-f5d4-409a-8e10-8ef1d55b98af

-- Generated from ChapterParity.lean — solution of BookProof.ChapterParity.antihermPart_isHermitian
import Mathlib
import Definitions.Def_ChapterParity
open BookProof.ChapterParity



open Matrix
open scoped ComplexConjugate

variable {n : Type*}

set_option maxHeartbeats 1000000 in
theorem solution (X : Matrix n n ℂ) : (antihermPart X).IsHermitian := by

  unfold Matrix.IsHermitian antihermPart
  rw [conjTranspose_smul, conjTranspose_sub, conjTranspose_conjTranspose,
      show (Xᴴ - X) = (-1 : ℂ) • (X - Xᴴ) by module, smul_smul]
  congr 1
  rw [star_inv₀]
  simp only [star_mul', Complex.star_def, map_ofNat, Complex.conj_I]
  have : (2 * Complex.I) ≠ 0 := by simp [Complex.I_ne_zero]
  field_simp
