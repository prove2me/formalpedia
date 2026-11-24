-- Prove2me | solution 1 for GaussianPerimeter.shiftedCapTail_measurable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T10:45:00.390291+00:00
-- url     : https://prove2.me/submissions/2150b0c7-c6fd-4d57-a93f-ba65322c6319

module
public import Definitions.Def_GaussianPerimeter_LimitBound
public import Definitions.Def_GaussianPerimeter_CapAsymptotics
public import Definitions.Def_GaussianPerimeter_Radial
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Definitions.Def_GaussianPerimeter_NazarovLimit
public import Theorems.Thm_GaussianPerimeter_capProfile_continuous


set_option autoImplicit true
@[expose] public section
public section
open Filter MeasureTheory
open scoped ENNReal Topology
open GaussianPerimeter
namespace GaussianPerimeter
theorem _root_.solution (a : ℝ) (n : ℕ) : Measurable (shiftedCapTail a n) := by
  change Measurable (fun w => shiftedCapTail a n w)
  by_cases hn : 2 ≤ n
  · simp only [shiftedCapTail, if_pos hn]
    have hInt := intervalIntegral.continuous_primitive (μ := volume)
      (capProfile_continuous hn).intervalIntegrable (1 : ℝ)
    have hFlip : Continuous (fun t : ℝ => ∫ u in t..1, capProfile n u) := by
      simpa only [intervalIntegral.integral_symm 1, Function.comp_def] using continuous_neg.comp hInt
    exact (hFlip.div_const _).measurable.comp (by
      unfold capThreshold capRadius
      fun_prop)
  · simp only [shiftedCapTail, if_neg hn]
    exact measurable_const
end GaussianPerimeter
