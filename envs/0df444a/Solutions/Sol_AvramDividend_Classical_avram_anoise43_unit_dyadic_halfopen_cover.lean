-- Prove2me | solution 1 for AvramDividend.Classical.avram_anoise43_unit_dyadic_halfopen_cover
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T14:24:10.061193+00:00
-- url     : https://prove2.me/submissions/81141e8b-0033-4b70-87fc-63004cd921e4

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
noncomputable section

/-- Every point in (-1,0] is covered by the right-closed dyadic unit mesh. -/
theorem solution
    (k : ℕ) (z : ℝ) (hzlo : -1 < z) (hzhi : z ≤ 0) :
    ∃ i : ℕ, i < 2 ^ k ∧
      z ∈ Ioc (-1 + (i : ℝ) / (2 : ℝ) ^ k)
        (-1 + ((i : ℝ) + 1) / (2 : ℝ) ^ k) := by
  classical
  let d : ℝ := (2 : ℝ) ^ k
  have hdpos : 0 < d := by dsimp [d]; positivity
  let a : ℝ := (z + 1) * d
  have ha0 : 0 < a := mul_pos (by linarith) hdpos
  have haub : a ≤ (2 : ℝ) ^ k := by
    dsimp [a, d]
    calc
      (z + 1) * (2 : ℝ) ^ k ≤ 1 * (2 : ℝ) ^ k :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = (2 : ℝ) ^ k := one_mul _
  let m : ℕ := Nat.ceil a
  have hmpos : 0 < m := Nat.ceil_pos.mpr ha0
  have hmle : m ≤ 2 ^ k := by
    apply Nat.ceil_le.mpr
    simpa [m] using haub
  have hmright : a ≤ (m : ℝ) := Nat.le_ceil a
  have hmleft : (m : ℝ) - 1 < a := by
    have h := Nat.ceil_lt_add_one (le_of_lt ha0)
    change (m : ℝ) < a + 1 at h
    linarith
  let i := m - 1
  have himem : i < 2 ^ k := by dsimp [i]; omega
  have hicast : (i : ℝ) + 1 = (m : ℝ) := by
    have heq : i + 1 = m := Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hmpos))
    exact_mod_cast heq
  refine ⟨i, himem, ?_⟩
  change -1 + (i : ℝ) / d < z ∧ z ≤ -1 + ((i : ℝ) + 1) / d
  constructor
  · have : (i : ℝ) < (z + 1) * d := by
      dsimp [a] at hmleft
      linarith
    apply (div_lt_iff₀ hdpos).mpr at this
    linarith
  · have : (z + 1) * d ≤ (i : ℝ) + 1 := by
      dsimp [a] at hmright
      linarith [hicast]
    have := (le_div_iff₀ hdpos).mpr this
    linarith
