-- Prove2me | solution 1 for AvramDividend.Classical.avram_oai_nonnegative_time_short_right_bridge_sequence_20261122
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T15:35:26.764894+00:00
-- url     : https://prove2.me/submissions/a5c98acf-1bdf-48aa-983b-326e12e089b2

import Mathlib
open Filter
open scoped NNReal Topology
noncomputable section
set_option autoImplicit false

theorem solution
    (s t : ℝ≥0) (hst : s < t) :
    ∃ r : ℕ → ℝ≥0,
      (∀ k, s < r k) ∧
      (∀ k, r k ≤ t) ∧
      Tendsto (fun k => r k - s) atTop (𝓝 0) ∧
      Tendsto (fun k => t - r k) atTop (𝓝 (t - s))  := by
  let r : ℕ → ℝ≥0 := fun k => s +
    (t - s) / ((k : ℝ≥0) + 1)
  have hGap : 0 < t - s := tsub_pos_iff_lt.mpr hst
  have hDiv : Tendsto
      (fun k : ℕ => (t - s) / ((k : ℝ≥0) + 1))
      atTop (𝓝 (0 : ℝ≥0)) := by
    have hOne : Tendsto (fun k : ℕ =>
        (1 : ℝ≥0) / ((k : ℝ≥0) + 1))
        atTop (𝓝 (0 : ℝ≥0)) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hConst : Tendsto (fun _ : ℕ => t - s) atTop (𝓝 (t - s)) :=
      tendsto_const_nhds
    simpa [div_eq_mul_inv, mul_assoc] using hConst.mul hOne
  have hTend : Tendsto r atTop (𝓝 s) := by
    have hConst : Tendsto (fun _ : ℕ => s) atTop (𝓝 s) :=
      tendsto_const_nhds
    simpa [r] using hConst.add hDiv
  refine ⟨r, ?_, ?_, ?_, ?_⟩
  · intro k
    dsimp [r]
    have hDen : 0 < (k : ℝ≥0) + 1 := by positivity
    exact lt_add_of_pos_right s (div_pos hGap hDen)
  · intro k
    dsimp [r]
    have hDen : (1 : ℝ≥0) ≤ (k : ℝ≥0) + 1 := by
      exact le_add_of_nonneg_left (show (0 : ℝ≥0) ≤ (k : ℝ≥0) from zero_le)
    calc
      s + (t - s) / ((k : ℝ≥0) + 1) ≤ s + (t - s) :=
        add_le_add_right (div_le_self (show (0 : ℝ≥0) ≤ t - s from zero_le) hDen) s
      _ = t := add_tsub_cancel_of_le hst.le
  · have h := hTend.sub
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => s) atTop (𝓝 s))
    simpa using h
  · exact (tendsto_const_nhds : Tendsto (fun _ : ℕ => t) atTop (𝓝 t)).sub hTend
