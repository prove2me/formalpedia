-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB167_original_finitecap_clipped_band_deriv_continuous
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T16:12:13.533478+00:00
-- url     : https://prove2.me/submissions/b942c018-48af-447e-b44b-2041fea9df84

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_gbB166_contdiff_two_open_set_derivative_continuousAt
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hFiniteCap : C ≠ ⊤)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ |
      0 < y ∧ ENNReal.ofReal y < C})
    (δ : ℝ) (hδ : 0 < δ) (j : ℕ) (y : ℝ)
    (hy : y ∈ Ioo (δ / 2)
      (C.toReal * (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ)))) :
    ContinuousAt (deriv w) y := by
  have hCpos : 0 < C.toReal :=
    ENNReal.toReal_pos (ne_of_gt hC) hFiniteCap
  have hfr : (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ)) < 1 := by
    apply (div_lt_one (by positivity)).2
    exact_mod_cast (by omega : j + 1 < j + 2)
  have hb : C.toReal * (((j + 1 : ℕ) : ℝ) /
      ((j + 2 : ℕ) : ℝ)) < C.toReal := by
    simpa only [mul_one] using (mul_lt_mul_of_pos_left hfr hCpos)
  have hypos : 0 < y := lt_trans (half_pos hδ) hy.1
  have hyC : ENNReal.ofReal y < C := by
    apply (ENNReal.ofReal_lt_iff_lt_toReal (le_of_lt hypos) hFiniteCap).2
    exact lt_trans hy.2 hb
  have hOpen : IsOpen {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C} := by
    exact (isOpen_lt continuous_const continuous_id).inter
      (isOpen_lt ENNReal.continuous_ofReal continuous_const)
  exact avram_gbB166_contdiff_two_open_set_derivative_continuousAt
    w _ hOpen hw_smooth y ⟨hypos, hyC⟩
