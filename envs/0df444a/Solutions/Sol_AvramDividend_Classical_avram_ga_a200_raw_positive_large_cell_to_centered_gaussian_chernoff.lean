-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a200_raw_positive_large_cell_to_centered_gaussian_chernoff
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T00:00:19.324967+00:00
-- url     : https://prove2.me/submissions/37f27170-f7d7-4a6c-ae0f-eb02c19924c4

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Real
noncomputable section

/-- Original Gaussian raw large-positive physical source increments yield a
uniform centred Chernoff threshold and a controlled deterministic drift factor. -/
theorem solution
    (θ δ σ d r : ℝ) (hθ : 0 ≤ θ) (hδ : 0 < δ)
    (hσ : 0 < σ) (hd : |d| ≤ δ / 2)
    (hr : δ ≤ r) :
    δ / (2 * σ) ≤ (r - d) / σ ∧
      Real.exp (θ * r) ≤
        Real.exp (θ * |d|) *
          Real.exp ((θ * σ) * ((r - d) / σ)) := by
  have hsmall : d ≤ δ / 2 := (le_abs_self d).trans hd
  have hzc : δ / 2 ≤ r - d := by linarith
  constructor
  · have hden : 0 < 2 * σ := by positivity
    apply (div_le_div_iff₀ hden hσ).2
    nlinarith
  · have hθd : θ * d ≤ θ * |d| :=
      mul_le_mul_of_nonneg_left (le_abs_self d) hθ
    have hExp : Real.exp (θ * d) ≤ Real.exp (θ * |d|) :=
      Real.exp_le_exp.mpr hθd
    have hid : (θ * σ) * ((r - d) / σ) = θ * (r - d) := by
      field_simp
    calc
      Real.exp (θ * r) =
          Real.exp (θ * d) * Real.exp (θ * (r - d)) := by
            rw [← Real.exp_add]
            congr 1
            ring
      _ ≤ Real.exp (θ * |d|) * Real.exp (θ * (r - d)) :=
        mul_le_mul_of_nonneg_right hExp (le_of_lt (Real.exp_pos _))
      _ = _ := by rw [hid]
