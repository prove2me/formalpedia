-- Prove2me | solution 1 for AvramDividend.Classical.avram_a21_original_finite_negative_small_mark_square_integrable_20261113
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T07:50:32.207206+00:00
-- url     : https://prove2.me/submissions/d4f8bf1c-ef90-4637-97dd-ea79431674e0

import Mathlib.MeasureTheory.Integral.IntegrableOn
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section

/-- The original finite negative jump measure integrates squared unit marks. -/
theorem solution
    (ν : Measure ℝ) (hFinite : ν (Iio (0 : ℝ)) ≠ ⊤) :
    IntegrableOn (fun z : ℝ => z ^ 2) (Ioo (-1 : ℝ) 0) ν := by
  have hMass : ν (Ioo (-1 : ℝ) 0) < ⊤ := by
    apply lt_of_le_of_lt (measure_mono ?_) (lt_top_iff_ne_top.mpr hFinite)
    intro z hz
    exact hz.2
  have hMeas : AEStronglyMeasurable (fun z : ℝ => z ^ 2)
      (ν.restrict (Ioo (-1 : ℝ) 0)) :=
    (measurable_id.pow_const 2).aestronglyMeasurable
  have hBound : ∀ᵐ z ∂(ν.restrict (Ioo (-1 : ℝ) 0)),
      ‖z ^ 2‖ ≤ (1 : ℝ) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with z hz
    rw [norm_pow, Real.norm_eq_abs]
    have hzmin : -1 < z := hz.1
    have hzmax : z < 0 := hz.2
    have habs : |z| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
    have hnonneg : 0 ≤ |z| := abs_nonneg z
    nlinarith [mul_nonneg (sub_nonneg.mpr habs)
      (add_nonneg hnonneg (by norm_num : (0 : ℝ) ≤ 1))]
  exact IntegrableOn.of_bound hMass hMeas 1 hBound
