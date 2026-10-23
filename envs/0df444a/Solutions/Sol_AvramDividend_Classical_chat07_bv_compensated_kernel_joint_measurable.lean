-- Prove2me | solution 1 for AvramDividend.Classical.chat07_bv_compensated_kernel_joint_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T07:48:45.455768+00:00
-- url     : https://prove2.me/submissions/b41fad9d-3789-45c4-b3e5-f3c188b45221

import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Order.Group.Lattice

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set

/-- The truncated compensated scale-jump kernel is jointly Borel measurable. -/
theorem solution
    (W : ℝ → ℝ) (hW : Monotone W) (θ : ℝ) :
    Measurable (fun p : ℝ × ℝ =>
      Real.exp (-(θ * p.1)) *
        |W (p.1 - p.2) - W p.1 +
          (if p.2 < 1 then p.2 * deriv W p.1 else 0)|) := by
  have hm : Measurable W := hW.measurable
  have hd : Measurable (deriv W) := measurable_deriv W
  have hfst : Measurable (fun p : ℝ × ℝ => p.1) := measurable_fst
  have hsnd : Measurable (fun p : ℝ × ℝ => p.2) := measurable_snd
  have hcut : MeasurableSet {p : ℝ × ℝ | p.2 < (1 : ℝ)} := by
    exact hsnd measurableSet_Iio
  have hcomp : Measurable (fun p : ℝ × ℝ =>
      if p.2 < (1 : ℝ) then p.2 * deriv W p.1 else 0) := by
    exact Measurable.ite hcut (hsnd.mul (hd.comp hfst)) measurable_const
  have hkernel : Measurable (fun p : ℝ × ℝ =>
      W (p.1 - p.2) - W p.1 +
        (if p.2 < 1 then p.2 * deriv W p.1 else 0)) := by
    exact ((hm.comp (hfst.sub hsnd)).sub (hm.comp hfst)).add hcomp
  exact (((measurable_const.mul hfst).neg).exp).mul hkernel.abs
