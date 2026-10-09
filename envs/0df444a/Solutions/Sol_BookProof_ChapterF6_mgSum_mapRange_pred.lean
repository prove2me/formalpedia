-- Prove2me | solution 1 for BookProof.ChapterF6.mgSum_mapRange_pred
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:06:01.324609+00:00
-- url     : https://prove2.me/submissions/a2cf209e-01a0-4992-ba53-5efb12b509e2

-- Generated from ChapterF6.lean — solution of BookProof.ChapterF6.mgSum_mapRange_pred
import Mathlib
import Definitions.Def_ChapterF6
open BookProof.ChapterF6



open scoped BigOperators


variable {α : Type*} [DecidableEq α]

variable {α : Type*} [DecidableEq α]

set_option maxHeartbeats 1000000 in
theorem solution (T : α →₀ ℕ) :
    mgSum (T.mapRange (fun n => n - 1) (by norm_num)) = mgSum T - T.support.card := by

  refine eq_tsub_of_add_eq ?_;
  unfold mgSum; simp only [implies_true, Finsupp.sum_mapRange_index] ;
  zify [ Finset.sum_add_distrib ];
  rw [ Finset.card_eq_sum_ones ] ;    rw [ Finsupp.sum, Finsupp.sum ] ; simp only [Finset.sum_const,
      smul_eq_mul, mul_one]  ; ring;
  rw [ Finset.sum_congr rfl fun x hx => Nat.cast_sub <| Nat.one_le_iff_ne_zero.mpr <|
      Finsupp.mem_support_iff.mp hx ] ; simp
