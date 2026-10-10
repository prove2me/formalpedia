-- Prove2me | solution 1 for BookProof.ChapterParity.hermPart_isHermitian
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T09:12:27.957002+00:00
-- url     : https://prove2.me/submissions/8eac435a-106a-4532-a820-d7b6c65904e3

-- Generated from ChapterParity.lean — solution of BookProof.ChapterParity.hermPart_isHermitian
import Mathlib
import Definitions.Def_ChapterParity
open BookProof.ChapterParity



open Matrix
open scoped ComplexConjugate

variable {n : Type*}

set_option maxHeartbeats 1000000 in
theorem solution (X : Matrix n n ℂ) : (hermPart X).IsHermitian := by

  unfold Matrix.IsHermitian hermPart
  rw [conjTranspose_smul, conjTranspose_add, conjTranspose_conjTranspose]
  simp [add_comm]
