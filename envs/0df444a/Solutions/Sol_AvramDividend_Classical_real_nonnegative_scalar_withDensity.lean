-- Prove2me | solution 1 for AvramDividend.Classical.real_nonnegative_scalar_withDensity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T11:35:03.121635+00:00
-- url     : https://prove2.me/submissions/af02e4f3-77ca-46ba-ae59-af32aea73f25

import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Data.ENNReal.Real
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal ENNReal

/-- A nonnegative real coefficient scales a real density in the expected way. -/
theorem solution (r : ℝ) (hr : 0 ≤ r) (k : ℝ → ℝ)
    (hkmeas : Measurable k) :
    ENNReal.ofReal r • volume.withDensity
      (fun x : ℝ => ENNReal.ofReal (k x)) =
    volume.withDensity (fun x : ℝ => ENNReal.ofReal (r * k x)) := by
  have hmeas : Measurable (fun x : ℝ => ENNReal.ofReal (k x)) :=
    ENNReal.measurable_ofReal.comp hkmeas
  calc
    ENNReal.ofReal r • volume.withDensity
        (fun x : ℝ => ENNReal.ofReal (k x)) =
      volume.withDensity (ENNReal.ofReal r •
        (fun x : ℝ => ENNReal.ofReal (k x))) :=
      (withDensity_smul (μ := (volume : Measure ℝ))
        (ENNReal.ofReal r) hmeas).symm
    _ = volume.withDensity (fun x : ℝ => ENNReal.ofReal (r * k x)) := by
      congr 1
      funext x
      simpa only [Pi.smul_apply, smul_eq_mul] using
        (ENNReal.ofReal_mul (p := r) (q := k x) hr).symm
