-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB240_original_finitecap_closed_clipped_band_deriv_continuous
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T10:05:54.530021+00:00
-- url     : https://prove2.me/submissions/0f117ef8-d5b8-4a81-a19c-e55c8daaf33b

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gbB166_contdiff_two_open_set_derivative_continuousAt
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The original C2 domain contains the whole closed prescribed clipping interval. -/
theorem solution
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hFiniteCap : C ≠ ⊤)
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (δ : ℝ) (hδ : 0 < δ) (j : ℕ) :
    ContinuousOn (deriv w)
      (Set.Icc (δ / 2)
        (C.toReal * (((j + 1 : ℕ) : ℝ) /
          ((j + 2 : ℕ) : ℝ)))) := by
  have hCpos : 0 < C.toReal :=
    ENNReal.toReal_pos (ne_of_gt hC) hFiniteCap
  have hfr : (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ)) < 1 := by
    apply (div_lt_one (by positivity)).2
    exact_mod_cast (by omega : j + 1 < j + 2)
  have hb : C.toReal * (((j + 1 : ℕ) : ℝ) /
      ((j + 2 : ℕ) : ℝ)) < C.toReal := by
    simpa only [mul_one] using (mul_lt_mul_of_pos_left hfr hCpos)
  have hOpen : IsOpen {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C} := by
    exact (isOpen_lt continuous_const continuous_id).inter
      (isOpen_lt ENNReal.continuous_ofReal continuous_const)
  intro y hy
  have hypos : 0 < y :=
    lt_of_lt_of_le (half_pos hδ) hy.1
  have hyC : ENNReal.ofReal y < C := by
    apply (ENNReal.ofReal_lt_iff_lt_toReal (le_of_lt hypos) hFiniteCap).2
    exact lt_of_le_of_lt hy.2 hb
  exact (avram_gbB166_contdiff_two_open_set_derivative_continuousAt
    w _ hOpen hw_smooth y ⟨hypos, hyC⟩).continuousWithinAt
