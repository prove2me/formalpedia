-- Prove2me | solution 1 for BlockCycleRotation.sum_reflect_bij
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T11:55:08.278128+00:00
-- url     : https://prove2.me/submissions/d60b6c4f-6d95-4635-b3f3-f1971becbd16

import Definitions.Def_BlockCycleRotation_Algorithm
import Definitions.Def_BlockCycleRotation_AllShifts
import Definitions.Def_BlockCycleRotation_Continuant
import Definitions.Def_BlockCycleRotation_Euclid
import Definitions.Def_BlockCycleRotation_ExpSum
import Mathlib

open Filter Topology Finset Real

namespace BlockCycleRotation

@[simp]
theorem remSum_zero (n : ℕ) : remSum n 0 = 0 := by
  rw [remSum]; simp

@[simp]
theorem norm_e (θ : ℝ) : ‖e θ‖ = 1 := Complex.norm_exp_ofReal_mul_I θ

@[simp]
theorem norm_e_pow (θ : ℝ) (n : ℕ) : ‖e θ ^ n‖ = 1 := by
  rw [norm_pow, norm_e, one_pow]

@[simp]
theorem cost_zero (n : ℕ) : cost n 0 = 0 := by
  rw [cost]; simp

@[simp]
theorem finalSeg_zero (n : ℕ) : finalSeg n 0 = n := by
  rw [finalSeg]; simp

@[simp]
theorem e_zero : e 0 = 1 := by simp [e]

@[simp] theorem K_nil : K [] = 1 := rfl

@[simp] theorem K_singleton (c : ℕ) : K [c] = c := rfl

@[simp] theorem cf_zero (a : ℕ) : cf a 0 = [] := by rw [cf]; simp

theorem mem_bigShifts {n k : ℕ} : k ∈ bigShifts n ↔ (1 ≤ k ∧ k ≤ n) ∧ n < 2 * k := by
  rw [bigShifts, Finset.mem_filter, Finset.mem_Icc]
  omega

theorem mem_smallShifts {n j : ℕ} : j ∈ smallShifts n ↔ j < n ∧ 2 * j < n := by
  rw [smallShifts, Finset.mem_filter, Finset.mem_range]

end BlockCycleRotation

open BlockCycleRotation in
/-- The reflection is a bijection between the upper-half shifts and the
strictly-lower-half ones. -/
theorem solution {n : ℕ} :
    ∑ k ∈ bigShifts n, remSum n (n - k) = ∑ j ∈ smallShifts n, remSum n j:= by
  refine Finset.sum_bij' (i := fun k _ => n - k) (j := fun j _ => n - j) ?_ ?_ ?_ ?_ ?_
  · intro k hk
    rw [mem_bigShifts] at hk
    rw [mem_smallShifts]
    omega
  · intro j hj
    rw [mem_smallShifts] at hj
    rw [mem_bigShifts]
    omega
  · intro k hk
    rw [mem_bigShifts] at hk
    omega
  · intro j hj
    rw [mem_smallShifts] at hj
    omega
  · intro k _
    rfl
