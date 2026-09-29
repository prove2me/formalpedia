-- Prove2me | solution 1 for BlockCycleRotation.seg_succ_prime
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T12:08:05.00429+00:00
-- url     : https://prove2.me/submissions/4d914ba3-9e9a-4d46-afbe-38e477144bd4

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

theorem Outt_mul_Inn (y : ℝ) : Outt y * Inn y = y * Int.fract (1 / y) := by
  unfold Outt Inn
  split_ifs with h
  · rw [h]; simp
  · have hg : (0 : ℝ) ≤ Int.fract (1 / y) := Int.fract_nonneg _
    have hden : (1 : ℝ) + Int.fract (1 / y) ≠ 0 := by positivity
    field_simp

@[simp]
theorem costB_zero (n b : ℕ) : costB n 0 b = 0 := by rw [costB]; simp

end BlockCycleRotation

open BlockCycleRotation in
/-- The one-step ratio of segments is `{1/Inⁱ(x)}`. -/
theorem solution (x : ℝ) (i : ℕ) :
    seg x (i + 1) = seg x i * Int.fract (1 / Inn^[i] x):= by
  unfold seg
  rw [Finset.prod_range_succ, Function.iterate_succ_apply']
  have h := Outt_mul_Inn (Inn^[i] x)
  calc (∏ m ∈ Finset.range i, Outt (Inn^[m] x)) * Outt (Inn^[i] x) * Inn (Inn^[i] x)
      = (∏ m ∈ Finset.range i, Outt (Inn^[m] x)) * (Outt (Inn^[i] x) * Inn (Inn^[i] x)) := by
        ring
    _ = (∏ m ∈ Finset.range i, Outt (Inn^[m] x)) * (Inn^[i] x * Int.fract (1 / Inn^[i] x)) := by
        rw [h]
    _ = (∏ m ∈ Finset.range i, Outt (Inn^[m] x)) * Inn^[i] x * Int.fract (1 / Inn^[i] x) := by
        ring
