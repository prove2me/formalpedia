-- Prove2me | solution 1 for BookProof.ChapterF6.mgT_sum_add
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:06:37.486103+00:00
-- url     : https://prove2.me/submissions/4d64b29b-154f-4818-b49f-a157b427f5de

-- Generated from ChapterF6.lean — solution of BookProof.ChapterF6.mgT_sum_add
import Mathlib
import Definitions.Def_ChapterF6
import Theorems.Thm_BookProof_ChapterF6_mgStep_card_le
import Theorems.Thm_BookProof_ChapterF6_mgSum_ge_card
import Theorems.Thm_BookProof_ChapterF6_mgSum_add_single
import Theorems.Thm_BookProof_ChapterF6_mgSum_mapRange_pred
open BookProof.ChapterF6



open scoped BigOperators


variable {α : Type*} [DecidableEq α]

variable {α : Type*} [DecidableEq α]

set_option maxHeartbeats 1000000 in
theorem solution (k : ℕ) (T : α →₀ ℕ) (s : List α) (hT : T.support.card ≤ k) :
    mgSum (mgT k T s) + (k + 1) * mgD k T s = mgSum T + s.length := by

  induction s generalizing T with
  | nil => ?_
  | cons x s ih => ?_
  · simp [ mgT, mgD ];
  · simp_all only [mgT, List.foldl_cons, mgD, List.length_cons];
    convert congr_arg ( · + ( k + 1 ) * ( if 0 < T x ∨ T.support.card < k then 0 else 1 ) ) ( ih (
                          mgStep k T x ) ( mgStep_card_le k T x hT ) ) using 1 ;
    focus (ring);
    split_ifs <;> simp_all only [mgStep, ↓reduceIte, mul_zero, add_zero, not_or, not_lt,
        nonpos_iff_eq_zero, lt_self_iff_false, false_or, mul_one];
    · rw [ mgSum_add_single ] ; ring;
    · rw [ if_neg ( by linarith ) ];
      rw [ mgSum_mapRange_pred ] ; ring;
      linarith [ Nat.sub_add_cancel ( show T.support.card ≤ mgSum T from mgSum_ge_card T ) ]
