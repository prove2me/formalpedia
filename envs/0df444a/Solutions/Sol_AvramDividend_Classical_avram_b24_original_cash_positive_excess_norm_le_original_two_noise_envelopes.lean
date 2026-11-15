-- Prove2me | solution 1 for AvramDividend.Classical.avram_b24_original_cash_positive_excess_norm_le_original_two_noise_envelopes
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T19:25:57.979017+00:00
-- url     : https://prove2.me/submissions/5347d748-e981-42e1-87ba-9ed4b45872b9

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem solution
    (F w G J BG BJ : ℝ)
    (hG : ‖G‖ ≤ BG) (hJ : ‖J‖ ≤ BJ) :
    ‖max (F - w - G - J) 0‖ ≤ ‖F‖ + ‖w‖ + BG + BJ := by
  have hf : F ≤ ‖F‖ := by
    rw [Real.norm_eq_abs]
    exact le_abs_self _
  have hw : -w ≤ ‖w‖ := by
    rw [Real.norm_eq_abs]
    exact neg_le_abs _
  have hg : -G ≤ BG := by
    calc
      -G ≤ ‖G‖ := by rw [Real.norm_eq_abs]; exact neg_le_abs _
      _ ≤ BG := hG
  have hj : -J ≤ BJ := by
    calc
      -J ≤ ‖J‖ := by rw [Real.norm_eq_abs]; exact neg_le_abs _
      _ ≤ BJ := hJ
  have hBg : 0 ≤ BG := (norm_nonneg _).trans hG
  have hBj : 0 ≤ BJ := (norm_nonneg _).trans hJ
  have hB : 0 ≤ ‖F‖ + ‖w‖ + BG + BJ := by positivity
  have hGap : F - w - G - J ≤ ‖F‖ + ‖w‖ + BG + BJ := by
    linarith only [hf, hw, hg, hj]
  have hMax : max (F - w - G - J) 0 ≤ ‖F‖ + ‖w‖ + BG + BJ :=
    max_le hGap hB
  have hPos : 0 ≤ max (F - w - G - J) 0 := le_max_right _ _
  simpa only [Real.norm_eq_abs, abs_of_nonneg hPos] using hMax
