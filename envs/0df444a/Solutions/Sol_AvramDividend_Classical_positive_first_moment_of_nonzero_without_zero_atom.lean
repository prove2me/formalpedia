-- Prove2me | solution 1 for AvramDividend.Classical.positive_first_moment_of_nonzero_without_zero_atom
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T09:27:59.021993+00:00
-- url     : https://prove2.me/submissions/aa32bae9-af97-4f85-8bfe-f18695787bf2

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.Data.ENNReal.Real
import Mathlib.Tactic.FunProp
open MeasureTheory Set
open scoped NNReal ENNReal
theorem solution (μ : Measure ℝ≥0)
    (hzero : μ ({0} : Set ℝ≥0) = 0) (hμ : μ ≠ 0) :
    0 < ∫⁻ z : ℝ≥0, ENNReal.ofReal (z : ℝ) ∂μ := by
  rw [pos_iff_ne_zero]
  intro h
  simp only [ENNReal.ofReal_coe_nnreal] at h
  rw [lintegral_eq_zero_iff (by measurability)] at h
  apply hμ
  rw [← Measure.measure_univ_eq_zero]
  have hne : μ {z : ℝ≥0 | z ≠ 0} = 0 := by
    rw [Filter.EventuallyEq, ae_iff] at h
    convert h using 2
    ext z
    simp
  refine le_antisymm ?_ (zero_le (a := μ univ))
  calc μ univ ≤ μ ({0} ∪ {z : ℝ≥0 | z ≠ 0}) := measure_mono (fun z _ => by
          by_cases hz : z = 0 <;> simp [hz])
    _ ≤ μ {0} + μ {z : ℝ≥0 | z ≠ 0} := measure_union_le _ _
    _ = 0 := by rw [hzero, hne, add_zero]
