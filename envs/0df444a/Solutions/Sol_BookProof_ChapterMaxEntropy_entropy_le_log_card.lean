-- Prove2me | solution 1 for BookProof.ChapterMaxEntropy.entropy_le_log_card
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T21:54:59.588828+00:00
-- url     : https://prove2.me/submissions/dff83c72-2a87-4535-9695-2233032cb127

-- Generated from ChapterMaxEntropy.lean — solution of BookProof.ChapterMaxEntropy.entropy_le_log_card
import Mathlib
import Definitions.Def_ChapterMaxEntropy
import Theorems.Thm_BookProof_ChapterMaxEntropy_negMulLog_sub_le
import Theorems.Thm_BookProof_ChapterDutchBook_Coherent_nonneg
import Definitions.Def_ChapterDutchBook
import Definitions.Def_ChapterIrreversible
open BookProof.ChapterMaxEntropy



open Real BigOperators Finset


variable {α : Type*} [Fintype α]

variable {α : Type*} [Fintype α]

set_option maxHeartbeats 1000000 in
theorem solution [Nonempty α] {p : α → ℝ} (hp : IsProb p) :
    entropy p ≤ Real.log (Fintype.card α) := by

  have hn : 0 < Fintype.card α := Fintype.card_pos
  have hnR : (Fintype.card α : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hsum : (∑ i, (Real.negMulLog (p i) - p i * Real.log (Fintype.card α)))
      ≤ ∑ i : α, ((Fintype.card α : ℝ)⁻¹ - p i) :=
    Finset.sum_le_sum (fun i _ => negMulLog_sub_le _ hn (hp.nonneg i))
  have lhs : (∑ i, (Real.negMulLog (p i) - p i * Real.log (Fintype.card α)))
      = entropy p - Real.log (Fintype.card α) := by
    rw [entropy, Finset.sum_sub_distrib, ← Finset.sum_mul, hp.sum_one, one_mul]
  have rhs : (∑ i : α, ((Fintype.card α : ℝ)⁻¹ - p i)) = 0 := by
    rw [Finset.sum_sub_distrib, hp.sum_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      mul_inv_cancel₀ hnR, sub_self]
  rw [lhs, rhs] at hsum
  linarith
