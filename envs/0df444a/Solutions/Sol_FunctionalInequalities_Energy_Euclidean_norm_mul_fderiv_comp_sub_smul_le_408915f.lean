-- Prove2me | solution 1 for FunctionalInequalities.Energy.Euclidean.norm_mul_fderiv_comp_sub_smul_le_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T15:51:21.759422+00:00
-- url     : https://prove2.me/submissions/e9531f6d-a759-4b66-8cfb-39d26dd37b24

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Cutoff_SmoothBall
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Lipschitz_Gradient
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Euclidean_LipschitzApproximation_Kernel
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Euclidean_LipschitzApproximation_Measurable
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Euclidean_WeakDerivative
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.FDeriv.Norm
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Topology.MetricSpace.Lipschitz

noncomputable section
open MeasureTheory Filter Topology
open scoped ContDiff
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Energy
end FunctionalInequalities.Energy
open FunctionalInequalities FunctionalInequalities.Energy
section
namespace FunctionalInequalities.Energy.Euclidean
end FunctionalInequalities.Energy.Euclidean
open FunctionalInequalities FunctionalInequalities.Energy FunctionalInequalities.Energy.Euclidean
universe u
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
namespace FunctionalInequalities.Energy.Euclidean
end FunctionalInequalities.Energy.Euclidean
open FunctionalInequalities.Energy.Euclidean in
/-- Domination of the translated derivative near `t` by an indicator of a compact thickening of
the support. -/
theorem solution {φ : V → ℝ} {M : ℝ}
    (hM : ∀ y, ‖fderiv ℝ φ y‖ ≤ M) (h : V → ℝ) (v : V) {t s : ℝ} (hs : dist s t < 1) (x : V) :
    ‖h x * fderiv ℝ φ (x - s • v) v‖ ≤
      (Metric.cthickening ((|t| + 1) * ‖v‖) (tsupport φ)).indicator
        (fun y => |h y| * (M * ‖v‖)) x := by
  by_cases hx : x ∈ Metric.cthickening ((|t| + 1) * ‖v‖) (tsupport φ)
  · rw [Set.indicator_of_mem hx]
    calc
      ‖h x * fderiv ℝ φ (x - s • v) v‖ =
          |h x| * ‖fderiv ℝ φ (x - s • v) v‖ := by
            rw [norm_mul, Real.norm_eq_abs]
      _ ≤ |h x| * (‖fderiv ℝ φ (x - s • v)‖ * ‖v‖) := by
            gcongr
            exact (fderiv ℝ φ (x - s • v)).le_opNorm v
      _ ≤ |h x| * (M * ‖v‖) := by
            gcongr
            exact hM _
  · rw [Set.indicator_of_notMem hx]
    have hzero : fderiv ℝ φ (x - s • v) = 0 := by
      by_contra hne
      have hy : x - s • v ∈ tsupport φ :=
        (support_fderiv_subset ℝ) (Function.mem_support.mpr hne)
      apply hx
      refine Metric.mem_cthickening_of_dist_le x (x - s • v)
        ((|t| + 1) * ‖v‖) _ hy ?_
      rw [dist_eq_norm, sub_sub_cancel, norm_smul, Real.norm_eq_abs]
      have hs' : |s - t| < 1 := by
        simpa [Real.dist_eq] using hs
      have htri : |s| ≤ |t| + |s - t| := by
        calc
          |s| = |t + (s - t)| := by
            congr 1
            ring
          _ ≤ |t| + |s - t| := by
            simpa only [Real.norm_eq_abs] using (norm_add_le t (s - t))
      have habs : |s| ≤ |t| + 1 := by
        have hlt : |s| < |t| + 1 := by
          linarith
        exact hlt.le
      exact mul_le_mul_of_nonneg_right habs (norm_nonneg v)
    rw [hzero]
    simp
