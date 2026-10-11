-- Prove2me | solution 1 for BookProof.SymmetryEntropy.negMulLog_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T16:10:30.54991+00:00
-- url     : https://prove2.me/submissions/fb7a10de-6c04-48a0-ad57-39aefa61baee

-- Generated from ChapterSymmetryEntropy.lean — solution of BookProof.SymmetryEntropy.negMulLog_eq_zero_iff
import Mathlib
import Definitions.Def_ChapterSymmetryEntropy
import Definitions.Def_ChapterMarkovEntropy
import Definitions.Def_ChapterReconstruct
open BookProof.SymmetryEntropy




open Finset
open BookProof.ChapterMarkovEntropy (entropy)
open BookProof.ChapterReconstruct (IsDeterministicCol)

variable {n : ℕ}

variable {n : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    Real.negMulLog x = 0 ↔ x = 0 ∨ x = 1 := by

  constructor
  · intro h
    rcases eq_or_lt_of_le h0 with h0' | h0'
    · exact Or.inl h0'.symm
    rcases eq_or_lt_of_le h1 with h1' | h1'
    · exact Or.inr h1'
    · exfalso
      have hlog : Real.log x < 0 := Real.log_neg h0' h1'
      have : 0 < Real.negMulLog x := by
        simp only [Real.negMulLog, neg_mul]
        nlinarith
      exact absurd h (ne_of_gt this)
  · rintro (rfl | rfl) <;> simp [Real.negMulLog]
