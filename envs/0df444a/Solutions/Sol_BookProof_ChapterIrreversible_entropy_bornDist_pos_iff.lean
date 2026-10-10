-- Prove2me | solution 1 for BookProof.ChapterIrreversible.entropy_bornDist_pos_iff
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T15:16:30.744998+00:00
-- url     : https://prove2.me/submissions/1886e965-0d85-4818-b4d4-e994a1b436f2

-- Generated from ChapterIrreversible.lean — solution of BookProof.ChapterIrreversible.entropy_bornDist_pos_iff
import Mathlib
import Definitions.Def_ChapterIrreversible
import Theorems.Thm_BookProof_ChapterIrreversible_bornDist_sum
import Theorems.Thm_BookProof_ChapterIrreversible_entropy_nonneg
import Theorems.Thm_BookProof_ChapterIrreversible_entropy_bornDist_eq_zero_iff
open BookProof.ChapterIrreversible



open scoped BigOperators
open Finset


variable {n : ℕ}

variable {n : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (v : Fin n → ℂ) (hv : ∑ a, ‖v a‖ ^ 2 = 1) :
    0 < entropy (bornDist v) ↔ ¬ IsDeterministicColumn v := by

  rw [ ← entropy_bornDist_eq_zero_iff v hv ];
  exact ⟨ fun h => ne_of_gt h,
    fun h => lt_of_le_of_ne
      ( entropy_nonneg _ ( fun a => sq_nonneg _ ) ( bornDist_sum v hv ) )
      ( Ne.symm h ) ⟩
