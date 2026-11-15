-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB39_interior_finite_cap_fraction_strict_band
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T13:41:32.426977+00:00
-- url     : https://prove2.me/submissions/e4a09d07-9b17-414d-85f5-e029f9d53a92

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set
noncomputable section

theorem solution
    (c : ℝ) (hc : 0 < c) (j : ℕ) :
    let b : ℝ := c * (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ))
    0 < b ∧ b < c := by
  let b : ℝ := c * (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ))
  have hnum : (0 : ℝ) < (j + 1 : ℕ) := by positivity
  have hden : (0 : ℝ) < (j + 2 : ℕ) := by positivity
  have hrpos : 0 < (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ)) :=
    div_pos hnum hden
  have hrlt : (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ)) < 1 := by
    apply (div_lt_one hden).2
    exact_mod_cast Nat.lt_succ_self (j + 1)
  constructor
  · exact mul_pos hc hrpos
  · nlinarith [mul_pos hc (sub_pos.mpr hrlt)]
