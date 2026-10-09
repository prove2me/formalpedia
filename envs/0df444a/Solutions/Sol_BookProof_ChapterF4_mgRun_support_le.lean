-- Prove2me | solution 1 for BookProof.ChapterF4.mgRun_support_le
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:03:44.199805+00:00
-- url     : https://prove2.me/submissions/def575d5-134c-4f0b-b58a-cc670998bb30

-- Generated from ChapterF4.lean — solution of BookProof.ChapterF4.mgRun_support_le
import Mathlib
import Definitions.Def_ChapterF4
import Theorems.Thm_BookProof_ChapterF4_mgStep_support_le
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
    mgSupport (mgRun k xs).1 ≤ k := by

      -- We proceed by induction on `xs`.
      induction xs with
      | nil => ?_
      | cons a xs ih => ?_
      · simp [ mgRun ];
        simp [ mgSupport ];
      · convert mgStep_support_le k ( mgRun k xs ) a ih using 1 <;> simp [mgRun]
