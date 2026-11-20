-- Prove2me | solution 2 for DeletionHash.MixedEdit.mixed_edit_codes
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:04:00.913898+00:00
-- url     : https://prove2.me/submissions/5cb8cc9d-f1d2-4165-81b3-9eb68b4aef1e

import Theorems.Thm_DeletionHash_MixedEdit_substring_edit_codes
open DeletionHash.MixedEdit

universe u

/-- Theorem 1.1: C is chosen before q, and N before the alphabet type. -/
theorem solution (t : ℕ) (ht : 2 ≤ t) :
    ∃ C : ℝ, 0 < C ∧ ∀ q : ℕ, 2 ≤ q → ∃ N : ℕ, q^q ≤ N ∧
      ∀ (α : Type u) [Fintype α] [DecidableEq α], Fintype.card α = q →
      ∀ n : ℕ, N ≤ n → ∃ code : Finset (Word α n), code.Nonempty ∧ Corrects 1 t code ∧
        redundancy q code ≤ ((2*t : ℝ)-1)*logBase q (n : ℝ) + C*logBase q (logBase q (n : ℝ)) := by exact DeletionHash.MixedEdit.substring_edit_codes t 1 ht (by decide)



#print axioms solution
