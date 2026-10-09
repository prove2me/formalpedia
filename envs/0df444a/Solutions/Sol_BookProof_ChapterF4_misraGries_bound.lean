-- Prove2me | solution 1 for BookProof.ChapterF4.misraGries_bound
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:04:36.702311+00:00
-- url     : https://prove2.me/submissions/af14ddbc-1a92-4011-9ec3-ee5838a184c6

-- Generated from ChapterF4.lean — solution of BookProof.ChapterF4.misraGries_bound
import Mathlib
import Definitions.Def_ChapterF4
import Theorems.Thm_BookProof_ChapterF4_mgRun_decrement_le
import Theorems.Thm_BookProof_ChapterF4_mgRun_undercount
import Theorems.Thm_BookProof_ChapterF4_mgRun_error_le
open BookProof.ChapterF4



open scoped BigOperators Matrix

variable {d k : ℕ}
variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [StarRing A] [ContinuousStar A]
  [CompleteSpace A] [StarModule ℂ A]
variable {α κ Ω : Type*} [Fintype α] [DecidableEq α] [Fintype κ] [DecidableEq κ]
  {mΩ : MeasurableSpace Ω}
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

set_option maxHeartbeats 1000000 in
theorem solution (k : ℕ) (hk : 0 < k) (xs : List ι) (x : ι) :
    (mgRun k xs).1 x ≤ xs.count x ∧
      xs.count x ≤ (mgRun k xs).1 x + xs.length / k := by

        refine ⟨mgRun_undercount k xs x, ?_⟩
        have hd : (mgRun k xs).2 ≤ xs.length / k :=
          (Nat.le_div_iff_mul_le hk).2 (by linarith [mgRun_decrement_le k xs])
        calc xs.count x ≤ (mgRun k xs).1 x + (mgRun k xs).2 := mgRun_error_le k xs x
          _ ≤ (mgRun k xs).1 x + xs.length / k := by omega
