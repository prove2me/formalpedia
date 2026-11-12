-- Prove2me | solution 1 for AvramDividend.Classical.avram_ja24_finite_negative_quadratic_integrable_on_unit_tail
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T17:13:25.981378+00:00
-- url     : https://prove2.me/submissions/10fdb7ff-603a-4895-9a86-c36ffb1f6374

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
noncomputable section

/-- A quadratic mark is bounded on the unit negative tail of a finite measure. -/
theorem solution
    (μ : Measure ℝ) (a : ℝ)
    (ha : (-1 : ℝ) ≤ a)
    (hFinite : μ (Iio (0 : ℝ)) ≠ ⊤) :
    IntegrableOn (fun z : ℝ => z ^ 2) (Ioo a 0) μ := by
  have hSubset : Ioo a 0 ⊆ Iio 0 := by
    intro z hz
    exact hz.2
  have hFin : μ (Ioo a 0) ≠ ⊤ := by
    have hUpper := lt_top_iff_ne_top.mpr hFinite
    exact (lt_of_le_of_lt (measure_mono hSubset) hUpper).ne
  have hMeas : AEStronglyMeasurable (fun z : ℝ => z ^ 2) μ :=
    (measurable_id.pow_const 2).aestronglyMeasurable
  have hBound : ∀ᵐ z ∂μ.restrict (Ioo a 0),
      ‖(z : ℝ) ^ 2‖ ≤ (1 : ℝ) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with z hz
    have hLower : (-1 : ℝ) < z := lt_of_le_of_lt ha hz.1
    have hUpper : z < 0 := hz.2
    have hSquare : z ^ 2 ≤ (1 : ℝ) := by nlinarith
    simpa [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg z)] using hSquare
  exact Measure.integrableOn_of_bounded hFin hMeas hBound
