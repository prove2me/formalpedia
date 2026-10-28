-- Prove2me | solution 1 for AvramDividend.Classical.geometric_atom_plus_real_density_full_cumulative
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T23:14:31.725293+00:00
-- url     : https://prove2.me/submissions/de0dccaf-85f5-4321-ac24-4186e89d3e6c

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.WithDensity
import Theorems.Thm_AvramDividend_Classical_geometric_atom_plus_real_density_zero_mass
import Theorems.Thm_AvramDividend_Classical_geometric_atom_plus_real_density_positive_cumulative

open MeasureTheory Set intervalIntegral


theorem solution
    (r : ℝ) (hr : 0 ≤ r) (f : ℝ → ℝ)
    (hfpos : ∀ y : ℝ, 0 ≤ f y)
    (β : Measure ℝ)
    (hβ : β = ENNReal.ofReal r • (Measure.dirac (0 : ℝ) +
      volume.withDensity (fun y : ℝ => ENNReal.ofReal (f y))))
    (hβneg : β (Iio (0 : ℝ)) = 0)
    (hβfin : β Set.univ ≠ ⊤)
    (x : ℝ) (hx : 0 < x)
    (hfi : IntervalIntegrable f volume 0 x) :
    (β (Iic x)).toReal = r + r * ∫ y in (0 : ℝ)..x, f y  := by 
  have h0 := AvramDividend.Classical.geometric_atom_plus_real_density_zero_mass r hr f β hβ
  have hpos := AvramDividend.Classical.geometric_atom_plus_real_density_positive_cumulative r hr f hfpos β hβ x hx.le hfi
  have hIic0 : β (Iic (0 : ℝ)) = ENNReal.ofReal r := by
    rw [← Set.Iio_union_right, measure_union (Set.disjoint_singleton_right.2 (by simp) : Disjoint (Iio (0:ℝ)) {0})
      (measurableSet_singleton 0), hβneg, h0, zero_add]
  have hsplit : β (Iic x) = β (Iic (0 : ℝ)) + β (Ioc (0 : ℝ) x) := by
    rw [← Set.Iic_union_Ioc_eq_Iic hx.le, measure_union (Set.Iic_disjoint_Ioc le_rfl) measurableSet_Ioc]
  have hfin : β (Ioc (0 : ℝ) x) ≠ ⊤ := ne_top_of_le_ne_top hβfin (measure_mono (Set.subset_univ _))
  rw [hsplit, hIic0, ENNReal.toReal_add ENNReal.ofReal_ne_top hfin, ENNReal.toReal_ofReal hr, hpos]
