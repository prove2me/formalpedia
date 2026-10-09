-- Prove2me | solution 1 for BookProof.ChapterF4.mgRun_error_le
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:04:35.81966+00:00
-- url     : https://prove2.me/submissions/9c3e7613-4905-4829-b4bf-a4849d6b2cb4

-- Generated from ChapterF4.lean — solution of BookProof.ChapterF4.mgRun_error_le
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
    xs.count x ≤ (mgRun k xs).1 x + (mgRun k xs).2 := by

      induction xs generalizing x with
      | nil => ?_
      | cons a xs ih => ?_
      all_goals simp_all only [List.count_nil, mgRun, add_zero, le_refl]
      by_cases hx : x = a <;> simp_all only [List.count_cons_self, Order.add_one_le_iff,
          List.count_cons, beq_iff_eq];
      · unfold mgStep; split_ifs <;> simp_all  ;
        · linarith [ ih a ];
        · grind;
        · grind;
      · unfold mgStep; split_ifs <;> simp_all  ;
        grind
