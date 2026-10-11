-- Prove2me | solution 1 for BookProof.SymmetryEntropy.entropy_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T16:10:31.905634+00:00
-- url     : https://prove2.me/submissions/890a48df-5cb0-4641-b438-1a6d975aa220

-- Generated from ChapterSymmetryEntropy.lean — solution of BookProof.SymmetryEntropy.entropy_nonneg
import Mathlib
import Definitions.Def_ChapterSymmetryEntropy
import Definitions.Def_ChapterMarkovEntropy
import Definitions.Def_ChapterReconstruct
import Definitions.Def_ChapterIrreversible
open BookProof.SymmetryEntropy




open Finset
open BookProof.ChapterMarkovEntropy (entropy)
open BookProof.ChapterReconstruct (IsDeterministicCol)

variable {n : ℕ}

variable {n : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution {p : Fin n → ℝ} (h0 : ∀ k, 0 ≤ p k) (h1 : ∀ k, p k ≤ 1) :
    0 ≤ entropy p := Finset.sum_nonneg fun k _ => Real.negMulLog_nonneg (h0 k) (h1 k)
