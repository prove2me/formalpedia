-- Prove2me | solution 1 for AvramDividend.Classical.avram_redux19_quadratic_collision_mesh_laplace_squeeze
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T00:17:32.386315+00:00
-- url     : https://prove2.me/submissions/6499782b-784a-4330-9fae-9024bbaaed58

import Mathlib.Analysis.SpecificLimits.Basic
import Theorems.Thm_AvramDividend_Classical_avram_redux19_quadratic_cell_collision_power_error
import Theorems.Thm_AvramDividend_Classical_avram_redux19_shifted_mesh_exp_limit
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter Topology AvramDividend.Classical
noncomputable section

/-! Quadratic cell collisions preserve the original short-cell exponential limit. -/
theorem solution
    (x C : ℝ) (a : ℕ → ℝ)
    (hC : 0 ≤ C)
    (ha : ∀ n : ℕ, 0 ≤ a n)
    (hab : ∀ n : ℕ, a n ≤ 1 - x / ((n : ℝ) + 1))
    (hb : ∀ n : ℕ, 1 - x / ((n : ℝ) + 1) ≤ 1)
    (hgap : ∀ n : ℕ, (1 - x / ((n : ℝ) + 1)) - a n ≤
      C / (((n + 1 : ℕ) : ℝ) ^ 2)) :
    Tendsto (fun n : ℕ => a n ^ (n + 1)) atTop (𝓝 (Real.exp (-x))) := by
  let b : ℕ → ℝ := fun n => 1 - x / ((n : ℝ) + 1)
  have hbound : ∀ n, 0 ≤ b n ^ (n + 1) - a n ^ (n + 1) ∧
      b n ^ (n + 1) - a n ^ (n + 1) ≤
        C / (((n + 1 : ℕ) : ℝ)) := by
    intro n
    have hb' : b n ≤ 1 := hb n
    have hab' : a n ≤ b n := hab n
    simpa only [b, Nat.cast_add, Nat.cast_one] using
      (avram_redux19_quadratic_cell_collision_power_error
        (a n) (b n) C n (ha n) hab' hb' hC
          (by simpa only [b, Nat.cast_add, Nat.cast_one] using hgap n))
  have hdecay : Tendsto (fun n : ℕ => C / (((n + 1 : ℕ) : ℝ)))
      atTop (𝓝 (0 : ℝ)) := by
    have h := (tendsto_const_div_atTop_nhds_zero_nat C).comp
      (Filter.tendsto_add_atTop_nat 1)
    simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using h
  have hdelta : Tendsto (fun n : ℕ =>
      b n ^ (n + 1) - a n ^ (n + 1)) atTop (𝓝 (0 : ℝ)) :=
    squeeze_zero (fun n => (hbound n).1)
      (fun n => (hbound n).2) hdecay
  have hbase : Tendsto (fun n : ℕ => b n ^ (n + 1))
      atTop (𝓝 (Real.exp (-x))) := by
    simpa only [b] using avram_redux19_shifted_mesh_exp_limit x
  have hlim := hbase.sub hdelta
  have heq : (fun n : ℕ =>
      b n ^ (n + 1) - (b n ^ (n + 1) - a n ^ (n + 1))) =
      (fun n : ℕ => a n ^ (n + 1)) := by
    funext n
    ring
  rw [heq] at hlim
  simpa only [sub_zero] using hlim
