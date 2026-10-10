-- Prove2me | solution 1 for BookProof.ChapterIrreversible.entropy_eq_zero_iff_pointMass
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T15:15:25.105129+00:00
-- url     : https://prove2.me/submissions/f230b132-c769-40c9-bcdf-b37475ca1b8f

-- Generated from ChapterIrreversible.lean — solution of BookProof.ChapterIrreversible.entropy_eq_zero_iff_pointMass
import Mathlib
import Definitions.Def_ChapterIrreversible
import Theorems.Thm_BookProof_ChapterIrreversible_entropy_pointMass_zero
import Theorems.Thm_BookProof_ChapterIrreversible_entropy_pos_of_not_pointMass
open BookProof.ChapterIrreversible



open scoped BigOperators
open Finset


variable {n : ℕ}

variable {n : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (p : Fin n → ℝ) (hnn : ∀ a, 0 ≤ p a)
    (hsum : ∑ a, p a = 1) : entropy p = 0 ↔ IsPointMass p := by

  refine ⟨ fun h => ?_, fun h => ?_ ⟩;
  · contrapose! h;
    exact ne_of_gt ( entropy_pos_of_not_pointMass p hnn hsum h );
  · exact entropy_pointMass_zero p h
