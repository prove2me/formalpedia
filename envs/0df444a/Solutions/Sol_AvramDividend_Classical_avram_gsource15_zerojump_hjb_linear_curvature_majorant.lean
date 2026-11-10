-- Prove2me | solution 1 for AvramDividend.Classical.avram_gsource15_zerojump_hjb_linear_curvature_majorant
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T16:47:14.641863+00:00
-- url     : https://prove2.me/submissions/719cbb69-5675-4f17-b479-ad6e1b6f2215

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f11_zero_jump_generator_eq_gaussian_drift
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (q : ℝ) (hq : 0 ≤ q)
    (w : ℝ → ℝ) (y : ℝ) (hσ : X.σ ≠ 0)
    (hw : 0 ≤ w y) (hwd : 0 ≤ deriv w y)
    (hHJB : X.generator w y - q * w y ≤ 0) :
    iteratedDeriv 2 w y ≤
      (2 * (q + |X.c|) / X.σ ^ 2) * (w y + deriv w y) := by
  have hs : 0 < X.σ ^ 2 := sq_pos_of_ne_zero hσ
  have hgen : X.σ ^ 2 / 2 * iteratedDeriv 2 w y +
      X.c * deriv w y ≤ q * w y := by
    rw [avram_p4_f11_zero_jump_generator_eq_gaussian_drift X hν w y] at hHJB
    linarith
  have habs : -|X.c| ≤ X.c := neg_abs_le X.c
  have hmul : (-|X.c|) * deriv w y ≤ X.c * deriv w y :=
    mul_le_mul_of_nonneg_right habs hwd
  have hqd : 0 ≤ q * deriv w y := mul_nonneg hq hwd
  have hcW : 0 ≤ |X.c| * w y := mul_nonneg (abs_nonneg _) hw
  have hB : X.σ ^ 2 / 2 * iteratedDeriv 2 w y ≤
      (q + |X.c|) * (w y + deriv w y) := by
    nlinarith
  calc
    iteratedDeriv 2 w y ≤
      (2 * (q + |X.c|) * (w y + deriv w y)) / X.σ ^ 2 := by
      apply (le_div_iff₀ hs).2
      nlinarith [hB]
    _ = (2 * (q + |X.c|) / X.σ ^ 2) *
        (w y + deriv w y) := by ring
