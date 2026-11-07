-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_meas7_finite_full_predictable_compact_bands
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T17:54:28.250988+00:00
-- url     : https://prove2.me/submissions/a90adb8d-67a2-4ead-977c-d42893f3bca9

import Mathlib.Data.ENNReal.Real
import Mathlib.Tactic.Positivity
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bv_meas7_finite_full_predictable_band_eventually_contains_reserve

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set AvramDividend.Classical
open scoped ENNReal
noncomputable section

/-- Explicit original finite-cap buffered bands have full predictable-mask
exhaustion: every strict interior reserve eventually enters [a_n,b_n]. -/
theorem solution (C : ℝ≥0∞) (hC : 0 < C) (hTop : C ≠ ⊤) :
    ∃ a b : ℕ → ℝ,
      (∀ n, 0 < a n) ∧
      (∀ n, a n ≤ 2) ∧
      (∀ n, a n ≤ b n) ∧
      (∀ n, Icc (a n / 2) (b n) ⊆
        {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) ∧
      (∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
        ∃ N : ℕ, ∀ n ≥ N, y ∈ Icc (a n) (b n)) := by
  have hc : 0 < C.toReal := ENNReal.toReal_pos (ne_of_gt hC) hTop
  let a : ℕ → ℝ := fun n => min 1 (C.toReal / 2) / ((n : ℝ) + 1)
  let b : ℕ → ℝ := fun n => C.toReal * ((n : ℝ) + 1) / ((n : ℝ) + 2)
  have hm : 0 < min (1 : ℝ) (C.toReal / 2) := by
    exact lt_min (by norm_num) (by linarith)
  have ha (n : ℕ) : 0 < a n := by
    change 0 < min (1 : ℝ) (C.toReal / 2) / ((n : ℝ) + 1)
    positivity
  have ha2 (n : ℕ) : a n ≤ 2 := by
    change min (1 : ℝ) (C.toReal / 2) / ((n : ℝ) + 1) ≤ 2
    have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    apply (div_le_iff₀ hn).2
    have hmin : min (1 : ℝ) (C.toReal / 2) ≤ 1 := min_le_left _ _
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    nlinarith
  have hac (n : ℕ) : a n ≤ C.toReal / 2 := by
    change min (1 : ℝ) (C.toReal / 2) / ((n : ℝ) + 1) ≤ C.toReal / 2
    have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    apply (div_le_iff₀ hn).2
    have hmin : min (1 : ℝ) (C.toReal / 2) ≤ C.toReal / 2 :=
      min_le_right _ _
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    nlinarith [mul_nonneg (le_of_lt hc) hn0]
  have hbc (n : ℕ) : C.toReal / 2 ≤ b n := by
    change C.toReal / 2 ≤ C.toReal * ((n : ℝ) + 1) / ((n : ℝ) + 2)
    have hn : (0 : ℝ) < (n : ℝ) + 2 := by positivity
    apply (le_div_iff₀ hn).2
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    nlinarith [mul_nonneg (le_of_lt hc) hn0]
  have hb_lt (n : ℕ) : b n < C.toReal := by
    change C.toReal * ((n : ℝ) + 1) / ((n : ℝ) + 2) < C.toReal
    have hn : (0 : ℝ) < (n : ℝ) + 2 := by positivity
    apply (div_lt_iff₀ hn).2
    nlinarith
  refine ⟨a, b, ha, ha2, (fun n => le_trans (hac n) (hbc n)), ?_, ?_⟩
  · intro n y hy
    rcases hy with ⟨hyl, hyu⟩
    change 0 < y ∧ ENNReal.ofReal y < C
    have hapos : 0 < a n / 2 := by positivity
    have hypos : 0 < y := lt_of_lt_of_le hapos hyl
    refine ⟨hypos, ?_⟩
    exact (ENNReal.ofReal_lt_iff_lt_toReal (le_of_lt hypos) hTop).2
      (lt_of_le_of_lt hyu (hb_lt n))
  · intro y hy hyC
    have hyc : y < C.toReal :=
      (ENNReal.ofReal_lt_iff_lt_toReal (le_of_lt hy) hTop).1 hyC
    exact avram_bv_meas7_finite_full_predictable_band_eventually_contains_reserve
      C.toReal (min 1 (C.toReal / 2)) y hc hm hy hyc
