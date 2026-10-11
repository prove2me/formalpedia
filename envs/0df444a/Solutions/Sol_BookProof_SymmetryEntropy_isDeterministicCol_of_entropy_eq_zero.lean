-- Prove2me | solution 1 for BookProof.SymmetryEntropy.isDeterministicCol_of_entropy_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T16:10:42.092986+00:00
-- url     : https://prove2.me/submissions/7c28e55d-1e82-4e29-903e-d7a25e9534f8

-- Generated from ChapterSymmetryEntropy.lean — solution of BookProof.SymmetryEntropy.isDeterministicCol_of_entropy_eq_zero
import Mathlib
import Definitions.Def_ChapterSymmetryEntropy
import Theorems.Thm_BookProof_SymmetryEntropy_entropy_eq_zero_iff
import Theorems.Thm_BookProof_SymmetryEntropy_bornCol_nonneg
import Theorems.Thm_BookProof_SymmetryEntropy_bornCol_le_one
import Theorems.Thm_BookProof_SymmetryEntropy_bornCol_eq_zero_iff
import Definitions.Def_ChapterMarkovEntropy
import Definitions.Def_ChapterIrreversible
import Definitions.Def_ChapterReconstruct
open BookProof.SymmetryEntropy




open Finset
open BookProof.ChapterMarkovEntropy (entropy)
open BookProof.ChapterReconstruct (IsDeterministicCol)

variable {n : ℕ}

variable {n : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution {U : Fin n → Fin n → ℂ} {a : Fin n}
    (hcol : ∑ k, ‖U k a‖ ^ 2 = 1) (h : entropy (bornCol U a) = 0) :
    IsDeterministicCol U a := by

  have hzeroone := (entropy_eq_zero_iff (bornCol_nonneg U a) (bornCol_le_one hcol)).mp h
  -- at most one index can carry the value `1`
  have hsum : ∑ k, bornCol U a k = 1 := hcol
  have hunique : ∀ l m : Fin n, l ≠ m → bornCol U a l = 0 ∨ bornCol U a m = 0 := by
    intro l m hlm
    rcases hzeroone l with hl | hl
    · exact Or.inl hl
    rcases hzeroone m with hm | hm
    · exact Or.inr hm
    · exfalso
      have hle : bornCol U a l + bornCol U a m ≤ ∑ k, bornCol U a k := by
        have := Finset.sum_le_sum_of_subset_of_nonneg
          (s := ({l, m} : Finset (Fin n))) (t := (univ : Finset (Fin n)))
          (f := bornCol U a) (Finset.subset_univ _)
          (fun k _ _ => bornCol_nonneg U a k)
        rwa [Finset.sum_pair hlm] at this
      rw [hsum, hl, hm] at hle
      norm_num at hle
  intro l m hlm
  rcases hunique l m hlm with h' | h'
  · rw [(bornCol_eq_zero_iff U a l).mp h']
    simp
  · rw [(bornCol_eq_zero_iff U a m).mp h']
    simp
