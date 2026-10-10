-- Prove2me | solution 1 for BookProof.ChapterIrreversible.entropy_pos_of_not_pointMass
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T15:15:13.142998+00:00
-- url     : https://prove2.me/submissions/9a914a3f-7b0e-492e-bb63-f110bc412204

-- Generated from ChapterIrreversible.lean — solution of BookProof.ChapterIrreversible.entropy_pos_of_not_pointMass
import Mathlib
import Definitions.Def_ChapterIrreversible
import Theorems.Thm_BookProof_ChapterIrreversible_le_one_of_prob
import Theorems.Thm_BookProof_ChapterIrreversible_exists_mem_Ioo_of_not_pointMass
open BookProof.ChapterIrreversible



open scoped BigOperators
open Finset


variable {n : ℕ}

variable {n : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (p : Fin n → ℝ) (hnn : ∀ a, 0 ≤ p a)
    (hsum : ∑ a, p a = 1) (hnp : ¬ IsPointMass p) : 0 < entropy p := by

  obtain ⟨ a, ha₁, ha₂ ⟩ := exists_mem_Ioo_of_not_pointMass p hnn hsum hnp;
  refine Finset.sum_pos'
    ( fun i _ => Real.negMulLog_nonneg ( hnn i ) ( le_one_of_prob p hnn hsum i ) )
    ⟨ a, Finset.mem_univ a, ?_ ⟩
  rw [ Real.negMulLog_def ] ; nlinarith [ Real.log_le_sub_one_of_pos ha₁ ]
