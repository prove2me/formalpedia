-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_main_public_small_mark_tsum_le_complement
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T09:36:51.075429+00:00
-- url     : https://prove2.me/submissions/01b945f8-5059-4b3d-ae2c-04826c1357b2

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter Set
open scoped BigOperators

/-- The actual original source jumps below a fixed mark cut-off are dominated
by the absolutely summable complement outside a selected finite mark set. -/
theorem solution
    {ι : Type*} [DecidableEq ι] (j : ι → ℝ) (S : Finset ι) (δ : ℝ)
    (hj : Summable (fun i => |j i|))
    (hS : ∀ i ∈ S, δ ≤ |j i|) :
    (∑' i : ι, if |j i| < δ then |j i| else 0) ≤
      ∑' i : ι, if i ∈ S then 0 else |j i| := by
  classical
  have hsmall_nonneg (i : ι) :
      0 ≤ (if |j i| < δ then |j i| else 0) := by
    split_ifs <;> positivity
  have hsmall_le (i : ι) :
      (if |j i| < δ then |j i| else 0) ≤ |j i| := by
    split_ifs <;> simp [abs_nonneg]
  have hunmarked_nonneg (i : ι) :
      0 ≤ (if i ∈ S then 0 else |j i|) := by
    split_ifs <;> positivity
  have hunmarked_le (i : ι) :
      (if i ∈ S then 0 else |j i|) ≤ |j i| := by
    split_ifs <;> simp [abs_nonneg]
  have hs : Summable (fun i : ι => if |j i| < δ then |j i| else 0) :=
    Summable.of_nonneg_of_le hsmall_nonneg hsmall_le hj
  have hu : Summable (fun i : ι => if i ∈ S then 0 else |j i|) :=
    Summable.of_nonneg_of_le hunmarked_nonneg hunmarked_le hj
  have hpoint (i : ι) :
      (if |j i| < δ then |j i| else 0) ≤
        (if i ∈ S then 0 else |j i|) := by
    by_cases hi : i ∈ S
    · have hnot : ¬ |j i| < δ := not_lt.mpr (hS i hi)
      simp [hi, hnot]
    · by_cases hδi : |j i| < δ
      · simp [hi, hδi]
      · simp [hi, hδi, abs_nonneg]
  exact Summable.tsum_le_tsum hpoint hs hu
