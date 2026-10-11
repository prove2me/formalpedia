-- Prove2me | solution 1 for BookProof.SymmetryEntropy.bornCol_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T16:10:39.186847+00:00
-- url     : https://prove2.me/submissions/831746c2-0182-45f1-a104-cf1471acd2a6

-- Generated from ChapterSymmetryEntropy.lean — solution of BookProof.SymmetryEntropy.bornCol_eq_zero_iff
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
theorem solution (U : Fin n → Fin n → ℂ) (a k : Fin n) :
    bornCol U a k = 0 ↔ U k a = 0 := by

  simp [bornCol, pow_eq_zero_iff]
