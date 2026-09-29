-- Prove2me | solution 1 for BlockCycleRotation.irrational_Inn
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T11:58:54.709756+00:00
-- url     : https://prove2.me/submissions/d1e62e19-c7c7-4576-be64-002b72c822a8

import Definitions.Def_BlockCycleRotation_Algorithm
import Definitions.Def_BlockCycleRotation_Continuant
import Definitions.Def_BlockCycleRotation_Euclid
import Definitions.Def_BlockCycleRotation_ExpSum
import Definitions.Def_BlockCycleRotation_Theorem10
import Mathlib

open Finset Real Filter Topology MeasureTheory BoxIntegral
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

theorem irrational_ne_zero {x : ℝ} (h : Irrational x) : x ≠ 0 := by
  intro hx
  exact Irrational.ne_int h 0 (by simp [hx])

theorem irrational_one_div {x : ℝ} (h : Irrational x) : Irrational (1 / x) := by
  rw [one_div]
  exact Irrational.inv h

theorem irrational_fract {x : ℝ} (h : Irrational x) : Irrational (Int.fract x) := by
  rw [Int.fract]
  exact Irrational.sub_intCast h _

end BlockCycleRotation

open BlockCycleRotation in
/-- **`In` preserves irrationality.** -/
theorem solution {x : ℝ} (h : Irrational x) : Irrational (Inn x):= by
  have hx0 : x ≠ 0 := irrational_ne_zero h
  have hg : Irrational (Int.fract (1 / x)) := irrational_fract (irrational_one_div h)
  have hgnn : (0 : ℝ) ≤ Int.fract (1 / x) := Int.fract_nonneg _
  have hglt : Int.fract (1 / x) < 1 := Int.fract_lt_one _
  unfold Inn
  rw [if_neg hx0]
  rintro ⟨q, hq⟩
  -- `g/(1+g) = q` forces `g = q/(1-q)`, which is rational
  have hden : (0 : ℝ) < 1 + Int.fract (1 / x) := by linarith
  have hqlt : (q : ℝ) < 1 := by
    rw [hq, div_lt_one hden]
    linarith
  have hq1 : (1 : ℝ) - (q : ℝ) ≠ 0 := by linarith
  refine hg ⟨q / (1 - q), ?_⟩
  have hmul : (q : ℝ) * (1 + Int.fract (1 / x)) = Int.fract (1 / x) := by
    rw [hq]
    field_simp
  push_cast
  rw [div_eq_iff (by exact_mod_cast hq1)]
  linarith [hmul]
