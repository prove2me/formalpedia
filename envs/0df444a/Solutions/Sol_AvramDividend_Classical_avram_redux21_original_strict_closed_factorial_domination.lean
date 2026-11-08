-- Prove2me | solution 1 for AvramDividend.Classical.avram_redux21_original_strict_closed_factorial_domination
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T10:11:52.469437+00:00
-- url     : https://prove2.me/submissions/5a6210e5-d386-41c6-bee5-0dc6f5bdfe2f

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_redux19_original_strict_negative_marked_times_finite
import Theorems.Thm_AvramDividend_Classical_avram_bv_jump8_turn10_strict_finite_set_card_le_closed

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-! The second factorial of an original strict jump count is bounded by
the second factorial of its original closed-cutoff count. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (T : ℝ≥0) (k : ℕ) :
    let a : ℕ :=
      (avram_redux19_original_strict_negative_marked_times_finite X ω T k).toFinset.card
    let b : ℕ := {u : ℝ≥0 | 0 < u ∧ u ≤ T ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
        -(1 / ((k : ℝ) + 1))}.ncard
    (a : ℝ) * ((a : ℝ) - 1) ≤ (b : ℝ) * ((b : ℝ) - 1) := by
  classical
  dsimp only
  let a : ℕ :=
    (avram_redux19_original_strict_negative_marked_times_finite X ω T k).toFinset.card
  let b : ℕ := {u : ℝ≥0 | 0 < u ∧ u ≤ T ∧
    X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
      -(1 / ((k : ℝ) + 1))}.ncard
  have hle_nat : a ≤ b :=
    avram_bv_jump8_turn10_strict_finite_set_card_le_closed X ω T k
  have hle : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hle_nat
  change (a : ℝ) * ((a : ℝ) - 1) ≤ (b : ℝ) * ((b : ℝ) - 1)
  by_cases ha : a = 0
  · by_cases hb : b = 0
    · simp [ha, hb]
    · have hbn : 1 ≤ b := by omega
      have hb_real : (1 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hbn
      simp only [ha, Nat.cast_zero, zero_sub, zero_mul]
      nlinarith
  · have han : 1 ≤ a := by omega
    have ha_real : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast han
    have hprod : 0 ≤ ((b : ℝ) - (a : ℝ)) *
        ((b : ℝ) + (a : ℝ) - 1) :=
      mul_nonneg (sub_nonneg.mpr hle) (by linarith)
    nlinarith
