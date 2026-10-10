-- Prove2me | solution 1 for BookProof.ChapterMarkovEntropy.applyMarkov_permMatrix
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T21:47:53.023538+00:00
-- url     : https://prove2.me/submissions/17148173-01a0-41a2-8b2a-2f4de74d07a6

-- Generated from ChapterMarkovEntropy.lean — solution of BookProof.ChapterMarkovEntropy.applyMarkov_permMatrix
import Mathlib
import Definitions.Def_ChapterMarkovEntropy
open BookProof.ChapterMarkovEntropy



open scoped BigOperators
open Finset


variable {n : ℕ}

variable {n : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (σ : Equiv.Perm (Fin n)) (p : Fin n → ℝ) :
    applyMarkov (permMatrix σ) p = fun j => p (σ.symm j) := by

  funext j
  unfold applyMarkov permMatrix
  rw [Finset.sum_eq_single (σ.symm j)] <;> aesop
