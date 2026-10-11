-- Prove2me | solution 1 for BookProof.SymmetryEntropy.bornCol_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T16:10:36.550021+00:00
-- url     : https://prove2.me/submissions/25f4281e-1404-4f27-9350-310ee934b8df

-- Generated from ChapterSymmetryEntropy.lean — solution of BookProof.SymmetryEntropy.bornCol_nonneg
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
theorem solution (U : Fin n → Fin n → ℂ) (a : Fin n) (k : Fin n) :
    0 ≤ bornCol U a k := by

  simp only [bornCol]
  positivity
