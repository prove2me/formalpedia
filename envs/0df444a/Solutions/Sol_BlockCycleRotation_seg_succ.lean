-- Prove2me | solution 1 for BlockCycleRotation.seg_succ
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T12:05:02.541147+00:00
-- url     : https://prove2.me/submissions/3d60339b-e3d4-491a-b188-6a0c42b46c8c

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

@[simp]
theorem costB_zero (n b : ℕ) : costB n 0 b = 0 := by rw [costB]; simp

end BlockCycleRotation

open BlockCycleRotation in
/-- The shift identity for segments. -/
theorem solution (x : ℝ) (i : ℕ) : seg x (i + 1) = Outt x * seg (Inn x) i:= by
  unfold seg
  rw [Finset.prod_range_succ']
  have hit : ∀ m : ℕ, Inn^[m] (Inn x) = Inn^[m + 1] x := by
    intro m
    rw [← Function.iterate_succ_apply]
  have hprod : ∏ m ∈ Finset.range i, Outt (Inn^[m] (Inn x))
      = ∏ m ∈ Finset.range i, Outt (Inn^[m + 1] x) :=
    Finset.prod_congr rfl fun m _ => by rw [hit]
  rw [hprod, hit i, Function.iterate_zero_apply]
  ring
