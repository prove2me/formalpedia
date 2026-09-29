-- Prove2me | solution 1 for BlockCycleRotation.buffer_helps
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T12:11:29.767393+00:00
-- url     : https://prove2.me/submissions/338ae0a1-c3d7-4a8e-8c0b-b517daf70b0a

import Definitions.Def_BlockCycleRotation_Algorithm
import Definitions.Def_BlockCycleRotation_Buffer
import Definitions.Def_BlockCycleRotation_Continuant
import Definitions.Def_BlockCycleRotation_Euclid
import Definitions.Def_BlockCycleRotation_ExpSum
import Definitions.Def_BlockCycleRotation_Theorem10
import Theorems.Thm_BlockCycleRotation_psi_rat
import Theorems.Thm_BlockCycleRotation_seg_succ
import Mathlib

open Finset Filter Topology Real MeasureTheory BoxIntegral
open scoped ENNReal

namespace BlockCycleRotation

@[simp]
theorem remSum_zero (n : ℕ) : remSum n 0 = 0 := by
  rw [remSum]; simp

/-- The defining recursion, in the form we actually use. -/
theorem remSum_of_pos {k : ℕ} (n : ℕ) (hk : k ≠ 0) :
    remSum n k = k + remSum k (n % k) := by
  rw [remSum]; simp [hk]

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

theorem seg_bufDepth_le {β x : ℝ} (h : ∃ i, seg x i ≤ β) : seg x (bufDepth β x) ≤ β :=
  Nat.sInf_mem h

theorem fCost_eq_of_le_half {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) : fCost x = 1 + psi x := by
  rw [fCost, min_eq_left (by linarith)]

theorem fract_five_halves : Int.fract ((5 : ℝ) / 2) = 1 / 2 := by
  have hfl : ⌊(5 : ℝ) / 2⌋ = 2 := by
    rw [Int.floor_eq_iff]
    norm_num
  rw [Int.fract, hfl]
  norm_num

theorem Outt_two_fifths : Outt (2 / 5 : ℝ) = 3 / 5 := by
  rw [Outt, if_neg (by norm_num)]
  rw [show (1 : ℝ) / (2 / 5) = 5 / 2 by norm_num, fract_five_halves]
  norm_num

theorem Inn_two_fifths : Inn (2 / 5 : ℝ) = 1 / 3 := by
  rw [Inn, if_neg (by norm_num)]
  rw [show (1 : ℝ) / (2 / 5) = 5 / 2 by norm_num, fract_five_halves]
  norm_num

theorem seg_two_fifths_one : seg (2 / 5 : ℝ) 1 = 1 / 5 := by
  rw [seg_succ, seg_zero, Outt_two_fifths, Inn_two_fifths]
  norm_num

theorem bufDepth_example : bufDepth (1 / 4 : ℝ) (2 / 5 : ℝ) = 1 := by
  have hmem : seg (2 / 5 : ℝ) 1 ≤ 1 / 4 := by rw [seg_two_fifths_one]; norm_num
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra hlt
  push_neg at hlt
  have h0 : bufDepth (1 / 4 : ℝ) (2 / 5 : ℝ) = 0 := by omega
  have h1 : seg (2 / 5 : ℝ) (bufDepth (1 / 4 : ℝ) (2 / 5 : ℝ)) ≤ 1 / 4 :=
    seg_bufDepth_le ⟨1, hmem⟩
  rw [h0, seg_zero] at h1
  norm_num at h1

theorem psi_two_fifths : psi (2 / 5 : ℝ) = 6 / 5 := by
  have h := psi_rat 2 5 (by norm_num) (by norm_num)
  have hrem : remSum 5 2 = 3 := by
    rw [remSum_of_pos 5 (by norm_num), show 5 % 2 = 1 from rfl,
      remSum_of_pos 2 (by norm_num), show 2 % 1 = 0 from rfl, remSum_zero]
  rw [hrem] at h
  norm_num at h
  linarith

@[simp]
theorem costB_zero (n b : ℕ) : costB n 0 b = 0 := by rw [costB]; simp

end BlockCycleRotation

open BlockCycleRotation in
/-- **The remark.**  With `β = 1/4` and a rotation by `x = 2/5`, neither segment
fits into the buffer, yet the buffered cost is strictly smaller. -/
theorem solution :
    (1 / 4 : ℝ) < 2 / 5 ∧ (1 / 4 : ℝ) < 1 - 2 / 5
      ∧ fCostBuf (1 / 4 : ℝ) (2 / 5 : ℝ) = 2 ∧ fCost (2 / 5 : ℝ) = 11 / 5:= by
  refine ⟨by norm_num, by norm_num, ?_, ?_⟩
  · rw [fCostBuf, psiBuf, bufDepth_example]
    rw [Finset.sum_range_one, seg_zero, seg_two_fifths_one]
    norm_num
  · rw [fCost_eq_of_le_half (by norm_num) (by norm_num), psi_two_fifths]
    norm_num
