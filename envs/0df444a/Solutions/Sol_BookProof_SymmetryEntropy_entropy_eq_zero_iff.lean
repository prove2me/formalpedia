-- Prove2me | solution 1 for BookProof.SymmetryEntropy.entropy_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T16:10:33.72646+00:00
-- url     : https://prove2.me/submissions/ae12aff1-27c2-4d28-a8db-2f95e44ea0a2

-- Generated from ChapterSymmetryEntropy.lean — solution of BookProof.SymmetryEntropy.entropy_eq_zero_iff
import Mathlib
import Definitions.Def_ChapterSymmetryEntropy
import Theorems.Thm_BookProof_SymmetryEntropy_negMulLog_eq_zero_iff
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
    entropy p = 0 ↔ ∀ k, p k = 0 ∨ p k = 1 := by

  constructor
  · intro h k
    have hterm : ∀ j ∈ (univ : Finset (Fin n)), 0 ≤ Real.negMulLog (p j) := fun j _ =>
      Real.negMulLog_nonneg (h0 j) (h1 j)
    have := (Finset.sum_eq_zero_iff_of_nonneg hterm).mp h k (mem_univ k)
    exact (negMulLog_eq_zero_iff (h0 k) (h1 k)).mp this
  · intro h
    refine Finset.sum_eq_zero fun k _ => ?_
    exact (negMulLog_eq_zero_iff (h0 k) (h1 k)).mpr (h k)
