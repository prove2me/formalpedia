-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_jump8_turn10_quadratic_shortcell_power_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T09:56:09.766427+00:00
-- url     : https://prove2.me/submissions/c9aafe07-10a6-4c06-ba34-a0114b69c3d2

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_redux19_quadratic_cell_collision_power_error

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter AvramDividend.Classical
open scoped Topology
noncomputable section

/-- A quadratic marked-collision error vanishes after multiplying over a mesh. -/
theorem solution
    (a C : ℝ) (q : ℕ → ℝ) (hC : 0 ≤ C)
    (hq : ∀ n, 0 ≤ q n ∧ q n ≤ 1)
    (hErr : ∀ n,
      0 ≤ q n - (1 - a / ((n + 1 : ℕ) : ℝ)) ∧
      q n - (1 - a / ((n + 1 : ℕ) : ℝ)) ≤
        C / ((n + 1 : ℕ) : ℝ) ^ 2) :
    Tendsto (fun n : ℕ => (q n) ^ (n + 1)) atTop
      (𝓝 (Real.exp (-a))) := by
  have hbase :
      Tendsto (fun n : ℕ =>
        (1 - a / ((n + 1 : ℕ) : ℝ)) ^ (n + 1))
        atTop (𝓝 (Real.exp (-a))) := by
    have h := (Real.tendsto_one_add_div_pow_exp (-a)).comp
      (Filter.tendsto_add_atTop_nat 1)
    simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one, neg_div, sub_eq_add_neg] using h
  have hsmall :
      Tendsto (fun n : ℕ => C / ((n + 1 : ℕ) : ℝ))
        atTop (𝓝 (0 : ℝ)) := by
    have hnat : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ))
        atTop atTop := by
      simpa only [Function.comp_def] using
        ((tendsto_natCast_atTop_atTop :
          Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).comp
            (Filter.tendsto_add_atTop_nat 1))
    have hinv := (tendsto_inv_atTop_zero.comp hnat).const_mul C
    simpa only [Function.comp_def, div_eq_mul_inv, mul_zero] using hinv
  have hupper :
      Tendsto (fun n : ℕ =>
        (1 - a / ((n + 1 : ℕ) : ℝ)) ^ (n + 1) +
          C / ((n + 1 : ℕ) : ℝ))
        atTop (𝓝 (Real.exp (-a))) := by
    simpa only [add_zero] using hbase.add hsmall
  obtain ⟨N, hN⟩ := exists_nat_gt a
  have hevent : ∀ᶠ n : ℕ in atTop,
      0 ≤ 1 - a / ((n + 1 : ℕ) : ℝ) := by
    filter_upwards [Filter.eventually_ge_atTop N] with n hn
    have hNr : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hnpos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
    apply sub_nonneg.mpr
    apply (div_le_iff₀ hnpos).2
    have hsucc : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
    rw [hsucc]
    linarith
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hbase hupper
  · filter_upwards [hevent] with n hn
    exact sub_nonneg.mp
      (avram_redux19_quadratic_cell_collision_power_error
        (1 - a / ((n + 1 : ℕ) : ℝ)) (q n) C n
        hn (sub_nonneg.mp (hErr n).1) (hq n).2 hC (hErr n).2).1
  · filter_upwards [hevent] with n hn
    have herror :
        (q n) ^ (n + 1) -
          (1 - a / ((n + 1 : ℕ) : ℝ)) ^ (n + 1) ≤
            C / ((n + 1 : ℕ) : ℝ) :=
      (avram_redux19_quadratic_cell_collision_power_error
        (1 - a / ((n + 1 : ℕ) : ℝ)) (q n) C n
        hn (sub_nonneg.mp (hErr n).1) (hq n).2 hC (hErr n).2).2
    linarith only [herror]
