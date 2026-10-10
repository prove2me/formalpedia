-- Prove2me | solution 1 for BookProof.ChapterRotaryPosition.rotaryEncode_add
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T18:10:39.394464+00:00
-- url     : https://prove2.me/submissions/0d25a189-02c6-49cc-8437-a9b0d81e73a1

-- Generated from ChapterRotaryPosition.lean — solution of BookProof.ChapterRotaryPosition.rotaryEncode_add
import Mathlib
import Definitions.Def_ChapterRotaryPosition
import Definitions.Def_ChapterCoherentOverlapComplex
open BookProof.ChapterRotaryPosition



open scoped BigOperators

noncomputable section


open BookProof.ChapterCoherentOverlapComplex

variable {n m : ℕ}

variable {n m : ℕ}


private theorem rotaryEncode_apply (omega : Fin n → ℝ) (p : ℝ) (q : EuclideanSpace ℂ (Fin n))
    (i : Fin n) :
    rotaryEncode omega p q i = Complex.exp ((p * omega i : ℝ) * Complex.I) * q i := rfl

set_option maxHeartbeats 1000000 in
theorem solution (omega : Fin n → ℝ) (p p' : ℝ) (q : EuclideanSpace ℂ (Fin n)) :
    rotaryEncode omega (p + p') q = rotaryEncode omega p (rotaryEncode omega p' q) := by

  ext i
  rw [rotaryEncode_apply, rotaryEncode_apply, rotaryEncode_apply, ← mul_assoc,
    ← Complex.exp_add]
  congr 2
  push_cast
  ring
