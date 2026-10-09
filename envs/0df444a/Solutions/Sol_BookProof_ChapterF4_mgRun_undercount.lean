-- Prove2me | solution 1 for BookProof.ChapterF4.mgRun_undercount
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:03:59.707797+00:00
-- url     : https://prove2.me/submissions/cbcee877-7835-430a-be25-8c621e7e837f

-- Generated from ChapterF4.lean — solution of BookProof.ChapterF4.mgRun_undercount
import Mathlib
import Definitions.Def_ChapterF4
open BookProof.ChapterF4



open scoped BigOperators Matrix

variable {d k : ℕ}
variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [StarRing A] [ContinuousStar A]
  [CompleteSpace A] [StarModule ℂ A]
variable {α κ Ω : Type*} [Fintype α] [DecidableEq α] [Fintype κ] [DecidableEq κ]
  {mΩ : MeasurableSpace Ω}
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

set_option maxHeartbeats 1000000 in
theorem solution (k : ℕ) (xs : List ι) (x : ι) :
    (mgRun k xs).1 x ≤ xs.count x := by

      induction xs generalizing x ; focus (simp_all [ mgRun ]);
      rename_i a l ih;
      by_cases h : 0 < (mgRun k l).1 a <;> simp_all only [mgRun, mgStep, ↓reduceIte, not_lt,
          nonpos_iff_eq_zero, lt_self_iff_false];
      · grind;
      · split_ifs <;> simp_all only [List.count_cons, beq_iff_eq, not_lt, tsub_le_iff_right];
        · grind;
        · exact le_add_of_le_of_nonneg ( le_add_of_le_of_nonneg ( ih x ) ( Nat.zero_le _ ) )
            zero_le_one
