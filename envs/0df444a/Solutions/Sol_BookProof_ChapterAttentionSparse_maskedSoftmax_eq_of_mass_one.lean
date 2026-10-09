-- Prove2me | solution 1 for BookProof.ChapterAttentionSparse.maskedSoftmax_eq_of_mass_one
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T18:41:41.440635+00:00
-- url     : https://prove2.me/submissions/ce3a5b89-25ab-472e-bd5d-01ade12eb899
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterAttentionSparse.lean — solution of BookProof.ChapterAttentionSparse.maskedSoftmax_eq_of_mass_one
import Mathlib
import Definitions.Def_ChapterAttentionSparse
import Theorems.Thm_BookProof_ChapterAttentionSparse_l1dist_maskedSoftmax_eq_zero_iff_mass_one
import Definitions.Def_ChapterAttentionMasking
import Definitions.Def_ChapterAttentionMarkov
open BookProof.ChapterAttentionMarkov
open BookProof.ChapterAttentionMasking
open BookProof.ChapterAttentionSparse



open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

set_option maxHeartbeats 1000000 in
theorem solution (beta : ℝ) (s : Fin m → ℝ) {S : Finset (Fin m)}
    (hS : S.Nonempty) (i : Fin m) (h : attendedMass beta s S = 1) (j : Fin m) :
    maskedSoftmax beta s S j = scoreSoftmax beta s j := by

  have hzero : l1dist (maskedSoftmax beta s S) (scoreSoftmax beta s) = 0 :=
    (l1dist_maskedSoftmax_eq_zero_iff_mass_one beta s hS i).2 h
  have hnn : ∀ l ∈ (Finset.univ : Finset (Fin m)),
      0 ≤ |maskedSoftmax beta s S l - scoreSoftmax beta s l| := fun l _ => abs_nonneg _
  have := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hzero j (Finset.mem_univ j)
  have := abs_eq_zero.1 this
  linarith
