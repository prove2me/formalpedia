-- Prove2me | solution 1 for BookProof.ChapterF4.mgRun_decrement_le
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:03:58.73313+00:00
-- url     : https://prove2.me/submissions/2f9b8273-7f7f-4830-93a1-f867a7fb7f3a

-- Generated from ChapterF4.lean — solution of BookProof.ChapterF4.mgRun_decrement_le
import Mathlib
import Definitions.Def_ChapterF4
import Theorems.Thm_BookProof_ChapterF4_mgRun_sum
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
    k * (mgRun k xs).2 ≤ xs.length := by

      have := mgRun_sum k xs;
      lia
