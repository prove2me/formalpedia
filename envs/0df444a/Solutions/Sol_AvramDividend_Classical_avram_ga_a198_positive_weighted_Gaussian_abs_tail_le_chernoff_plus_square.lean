-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a198_positive_weighted_Gaussian_abs_tail_le_chernoff_plus_square
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T23:19:07.997493+00:00
-- url     : https://prove2.me/submissions/a54fa2aa-cfdf-49d3-8b25-938812bcf662

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.Positivity
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Real
noncomputable section

/-- A Gaussian weighted absolute large-tail requires a positive Esscher
tilt only: control the negative tail using its ordinary squared energy. -/
theorem solution
    (θ r δ z : ℝ) (hθ : 0 ≤ θ) (hr : 0 ≤ r) (hδ : 0 < δ) :
    (if δ ≤ |z| then Real.exp (θ * z) else 0) ≤
      Real.exp (-r * δ) * Real.exp ((θ + r) * z) +
        (if δ ≤ |z| then z^2 / δ^2 else 0) := by
  by_cases ht : δ ≤ |z|
  · simp only [if_pos ht]
    by_cases hz : 0 ≤ z
    · have hlarge : δ ≤ z := by simpa [abs_of_nonneg hz] using ht
      have hlin : θ * z ≤ -r * δ + (θ + r) * z := by
        nlinarith [mul_nonneg hr (sub_nonneg.mpr hlarge)]
      have he : Real.exp (θ * z) ≤
          Real.exp (-r * δ) * Real.exp ((θ + r) * z) := by
        rw [← Real.exp_add]
        exact Real.exp_le_exp.mpr hlin
      have hs : 0 ≤ z^2 / δ^2 :=
        div_nonneg (sq_nonneg _) (sq_nonneg _)
      linarith
    · have hneg : z ≤ 0 := le_of_not_ge hz
      have hlarge : δ ≤ -z := by
        simpa [abs_of_nonpos hneg] using ht
      have hp1 : 0 ≤ -z - δ := by linarith
      have hp2 : 0 ≤ -z + δ := by linarith
      have hsq : δ^2 ≤ z^2 := by
        nlinarith [mul_nonneg hp1 hp2]
      have hd : 1 ≤ z^2 / δ^2 := by
        exact (le_div_iff₀ (sq_pos_of_pos hδ)).2 (by nlinarith)
      have he : Real.exp (θ * z) ≤ 1 := by
        exact (Real.exp_le_one_iff).2 (mul_nonpos_of_nonneg_of_nonpos hθ hneg)
      have hp : 0 ≤ Real.exp (-r * δ) * Real.exp ((θ + r) * z) := by
        positivity
      linarith
  · simp only [if_neg ht]
    positivity
