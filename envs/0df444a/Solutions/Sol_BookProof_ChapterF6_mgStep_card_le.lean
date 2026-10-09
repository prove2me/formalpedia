-- Prove2me | solution 1 for BookProof.ChapterF6.mgStep_card_le
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:05:03.953579+00:00
-- url     : https://prove2.me/submissions/e7f3c9bd-4eb2-4bc3-9a4e-cc9753ddac32

-- Generated from ChapterF6.lean — solution of BookProof.ChapterF6.mgStep_card_le
import Mathlib
import Definitions.Def_ChapterF6
open BookProof.ChapterF6



open scoped BigOperators


variable {α : Type*} [DecidableEq α]

variable {α : Type*} [DecidableEq α]

set_option maxHeartbeats 1000000 in
theorem solution (k : ℕ) (T : α →₀ ℕ) (x : α) (hT : T.support.card ≤ k) :
    (mgStep k T x).support.card ≤ k := by

  classical
  refine le_trans ( Finset.card_le_card (t := ?_) ?_ ) ?_;
  focus (exact if 0 < T x ∨ T.support.card < k then insert x T.support else T.support);
  · intro y hy; split_ifs <;> simp_all only [mgStep, ↓reduceIte, Finsupp.mem_support_iff,
      Finsupp.coe_add, Pi.add_apply, ne_eq, Nat.add_eq_zero_iff, not_and, Finset.mem_insert,
          Finsupp.mapRange_apply, not_or, not_lt, nonpos_iff_eq_zero] ;
    · contrapose! hy; aesop;
    · exact fun h => hy <| by simp [ h ] ;
  · grind
