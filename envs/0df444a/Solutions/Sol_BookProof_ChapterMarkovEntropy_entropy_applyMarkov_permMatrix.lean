-- Prove2me | solution 1 for BookProof.ChapterMarkovEntropy.entropy_applyMarkov_permMatrix
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T21:48:27.980157+00:00
-- url     : https://prove2.me/submissions/157f9c0b-9390-4af8-8170-8ba436b9483a

-- Generated from ChapterMarkovEntropy.lean — solution of BookProof.ChapterMarkovEntropy.entropy_applyMarkov_permMatrix
import Mathlib
import Definitions.Def_ChapterMarkovEntropy
import Theorems.Thm_BookProof_ChapterMarkovEntropy_applyMarkov_permMatrix
import Definitions.Def_ChapterIrreversible
open BookProof.ChapterMarkovEntropy



open scoped BigOperators
open Finset


variable {n : ℕ}

variable {n : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (σ : Equiv.Perm (Fin n)) (p : Fin n → ℝ) :
    entropy (applyMarkov (permMatrix σ) p) = entropy p := by

  rw [applyMarkov_permMatrix]
  exact Equiv.sum_comp σ.symm (fun j => Real.negMulLog (p j))
