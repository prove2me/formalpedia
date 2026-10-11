-- Prove2me | solution 1 for BookProof.SymmetryEntropy.exists_eq_one_of_isDeterministicCol
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T16:10:40.542896+00:00
-- url     : https://prove2.me/submissions/b5ca64f3-1048-4994-8a54-07e6e346e4bb

-- Generated from ChapterSymmetryEntropy.lean — solution of BookProof.SymmetryEntropy.exists_eq_one_of_isDeterministicCol
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
theorem solution {U : Fin n → Fin n → ℂ} {a : Fin n}
    (hcol : ∑ k, ‖U k a‖ ^ 2 = 1) (hdet : IsDeterministicCol U a) :
    ∃ k, bornCol U a k = 1 ∧ ∀ l, l ≠ k → bornCol U a l = 0 := by

  have hne : ∃ k, U k a ≠ 0 := by
    by_contra hall
    push_neg at hall
    have hz : ∑ k, ‖U k a‖ ^ 2 = 0 := by
      refine Finset.sum_eq_zero fun k _ => ?_
      rw [hall k]
      simp
    rw [hz] at hcol
    norm_num at hcol
  obtain ⟨k, hk⟩ := hne
  have hzero : ∀ l, l ≠ k → U l a = 0 := by
    intro l hl
    have := hdet l k hl
    rcases mul_eq_zero.mp this with h | h
    · exact absurd ((starRingEnd ℂ).injective (by simpa using h)) hk
    · exact h
  refine ⟨k, ?_, fun l hl => by simp [bornCol, hzero l hl]⟩
  have : ∑ j, ‖U j a‖ ^ 2 = ‖U k a‖ ^ 2 := by
    refine Finset.sum_eq_single k (fun j _ hj => by rw [hzero j hj]; simp) (by simp)
  rw [this] at hcol
  simpa [bornCol] using hcol
