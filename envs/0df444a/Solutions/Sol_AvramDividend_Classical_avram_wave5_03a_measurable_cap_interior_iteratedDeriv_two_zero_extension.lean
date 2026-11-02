-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_03a_measurable_cap_interior_iteratedDeriv_two_zero_extension
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T21:10:21.881815+00:00
-- url     : https://prove2.me/submissions/2ce998ea-ccf1-4294-b4cc-939d6354eb0b

import Mathlib
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Topology AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

/-- Measurable exact-cap zero extension of the smooth HJB second derivative. -/
theorem solution
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) :
    Measurable (fun y : ℝ =>
      if 0 < y ∧ ENNReal.ofReal y < C then iteratedDeriv 2 w y else 0) := by
  classical
  let s : Set ℝ := {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}
  change ContDiffOn ℝ 2 w s at hw
  have hOpen : IsOpen s := by
    change IsOpen (Ioi (0 : ℝ) ∩ ENNReal.ofReal ⁻¹' Iio C)
    exact isOpen_Ioi.inter (isOpen_Iio.preimage ENNReal.continuous_ofReal)
  have hWithin : ContinuousOn (iteratedDerivWithin 2 w s) s :=
    hw.continuousOn_iteratedDerivWithin (by norm_num) hOpen.uniqueDiffOn
  have hCont : ContinuousOn (iteratedDeriv 2 w) s := by
    apply hWithin.congr
    intro y hy
    exact (iteratedDerivWithin_of_isOpen hOpen hy).symm
  change Measurable (s.piecewise (iteratedDeriv 2 w) (fun _ => (0 : ℝ)))
  exact hCont.measurable_piecewise continuous_const.continuousOn hOpen.measurableSet
