-- Prove2me | solution 1 for BlockCycleRotation.expected_cost_half_buffer
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T12:13:52.657813+00:00
-- url     : https://prove2.me/submissions/0b75ba30-8515-4510-ba29-a5a10421ed95

import Definitions.Def_BlockCycleRotation_Algorithm
import Definitions.Def_BlockCycleRotation_Buffer
import Definitions.Def_BlockCycleRotation_Continuant
import Definitions.Def_BlockCycleRotation_Euclid
import Definitions.Def_BlockCycleRotation_ExpSum
import Definitions.Def_BlockCycleRotation_Theorem10
import Mathlib

open Finset Filter Topology Real MeasureTheory BoxIntegral
open scoped ENNReal

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

theorem seg_zero (x : ℝ) : seg x 0 = x := by
  unfold seg
  simp

theorem bufDepth_eq_zero {β x : ℝ} (h : x ≤ β) : bufDepth β x = 0 :=
  Nat.eq_zero_of_le_zero (Nat.sInf_le (by rw [Set.mem_setOf_eq, seg_zero]; exact h))

/-- **The terminating branch.** -/
theorem psiBuf_of_le {β x : ℝ} (h : x ≤ β) : psiBuf β x = x := by
  rw [psiBuf, bufDepth_eq_zero h, seg_zero]
  simp

theorem psiBuf_half {x : ℝ} (hx : x ≤ 1 / 2) : psiBuf (1 / 2) x = x :=
  psiBuf_of_le hx

theorem fCostBuf_half {x : ℝ} (hx : x ≤ 1 / 2) : fCostBuf (1 / 2) x = 1 + x := by
  rw [fCostBuf, psiBuf_half hx]

@[simp]
theorem costB_zero (n b : ℕ) : costB n 0 b = 0 := by rw [costB]; simp

end BlockCycleRotation

open BlockCycleRotation in
/-- **The figure's `1.25`.**  With a buffer of half the array, the expected cost
is `5/4` moves per element. -/
theorem solution :
    2 * ∫ x in (0 : ℝ)..(1 / 2), fCostBuf (1 / 2) x = 5 / 4:= by
  have hcongr : ∫ x in (0 : ℝ)..(1 / 2), fCostBuf (1 / 2) x
      = ∫ x in (0 : ℝ)..(1 / 2), (1 + x) := by
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2), Set.mem_Icc] at hx
    exact fCostBuf_half hx.2
  rw [hcongr, intervalIntegral.integral_add intervalIntegrable_const
    intervalIntegral.intervalIntegrable_id, intervalIntegral.integral_const, integral_id]
  norm_num
