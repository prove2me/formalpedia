-- Prove2me | solution 1 for BookProof.ChapterF4.mgRun_sum
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:03:45.336673+00:00
-- url     : https://prove2.me/submissions/e933f630-c861-453b-8026-d5d6e2917b89

-- Generated from ChapterF4.lean — solution of BookProof.ChapterF4.mgRun_sum
import Mathlib
import Definitions.Def_ChapterF4
import Theorems.Thm_BookProof_ChapterF4_mgSum_decrement
import Theorems.Thm_BookProof_ChapterF4_mgRun_support_le
open BookProof.ChapterF4



open scoped BigOperators Matrix

variable {d k : ℕ}
variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [StarRing A] [ContinuousStar A]
  [CompleteSpace A] [StarModule ℂ A]
variable {α κ Ω : Type*} [Fintype α] [DecidableEq α] [Fintype κ] [DecidableEq κ]
  {mΩ : MeasurableSpace Ω}
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

set_option maxHeartbeats 1000000 in
theorem solution (k : ℕ) (xs : List ι) :
    (∑ a, (mgRun k xs).1 a) + (k + 1) * (mgRun k xs).2 = xs.length := by

      induction xs with
      | nil => ?_
      | cons xs ih _ih => ?_
      · simp [ mgRun ];
      · rw [ show mgRun k ( xs :: ih ) = mgStep k ( mgRun k ih ) xs from rfl ];
        unfold mgStep; split_ifs <;> simp_all only [List.length_cons, not_lt, nonpos_iff_eq_zero,
            mgSupport] ;
        · simp only [Finset.mem_univ, Finset.sum_update_of_mem];
          rw [ ← Finset.sum_sdiff ( Finset.subset_univ { xs } ) ] at * ;            simp_all [
              Finset.sum_singleton ] ; linarith;
        · simp only [Finset.mem_univ, Finset.sum_update_of_mem]
          have hsub : ∑ x ∈ Finset.univ \ {xs}, (mgRun k ih).1 x = ∑ a, (mgRun k ih).1 a := by
            rw [← Finset.sum_sdiff (Finset.subset_univ {xs})]
            simp [Finset.sum_singleton]
            linarith
          rw [hsub, add_assoc, _ih]
          ring
        · have := mgSum_decrement ( mgRun k ih |>.1 ) ; simp_all [ mgSupport ] ;
          linarith [ show Finset.card ( Finset.filter ( fun a => 0 < ( mgRun k ih |>.1 ) a )
              Finset.univ ) = k from le_antisymm ( mgRun_support_le k ih ) ‹_› ]
