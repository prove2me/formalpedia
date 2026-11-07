-- Prove2me | solution 1 for AvramDividend.Classical.avram_redux19_unit_interval_power_lipschitz
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T23:38:52.119326+00:00
-- url     : https://prove2.me/submissions/ad8c618d-b0aa-4267-804f-ea5e1e7bb4aa

import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.SetSemiring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
noncomputable section

/-! A uniform n-Lipschitz bound for powers of subunit short-cell expectations. -/
theorem solution (a b : ℝ) (n : ℕ)
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    0 ≤ b ^ n - a ^ n ∧
      b ^ n - a ^ n ≤ (n : ℝ) * (b - a) := by
  have hb0 : 0 ≤ b := le_trans ha hab
  induction n with
  | zero => simp
  | succ n ih =>
    have han : 0 ≤ a ^ n := pow_nonneg ha n
    have han1 : a ^ n ≤ 1 := pow_le_one₀ ha (le_trans hab hb)
    have hdiff : 0 ≤ b - a := sub_nonneg.mpr hab
    have hpow : b ^ (n + 1) - a ^ (n + 1) =
        b * (b ^ n - a ^ n) + (b - a) * a ^ n := by
      rw [pow_succ, pow_succ]
      ring
    have hsmall : b * (b ^ n - a ^ n) ≤ b ^ n - a ^ n := by
      have := mul_nonneg (sub_nonneg.mpr hb) ih.1
      nlinarith
    have hsmall' : (b - a) * a ^ n ≤ b - a := by
      have := mul_nonneg hdiff (sub_nonneg.mpr han1)
      nlinarith
    constructor
    · rw [hpow]
      exact add_nonneg (mul_nonneg hb0 ih.1) (mul_nonneg hdiff han)
    · rw [hpow]
      push_cast
      nlinarith [ih.2]
