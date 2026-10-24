-- Prove2me | solution 1 for FunctionalInequalities.Energy.locallyLipschitz_mul_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T15:55:59.460638+00:00
-- url     : https://prove2.me/submissions/f7439492-9bed-4f17-ad66-24129b42fefe

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Cutoff_SmoothBall
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Lipschitz_Gradient
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Euclidean_LipschitzApproximation_Approximation
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Euclidean_LipschitzApproximation_Kernel
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Euclidean_LipschitzApproximation_Measurable
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Euclidean_Slope_Recovery
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Form_Functional
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_LocalSlope_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_LocalSlope_Relaxation
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Relaxation_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_SmoothGradient_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_SmoothGradient_Intrinsic_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_L2_MeanVariance
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_AffineSupport
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.FDeriv.Norm
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Analysis.Normed.Affine.Isometry
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.ENNReal.Inv
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.Probability.Moments.Variance
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Sequences

noncomputable section
open MeasureTheory Filter Topology Set
open FunctionalInequalities.Energy.Euclidean.LipschitzApproximation
open scoped ENNReal NNReal ContDiff
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Energy
end FunctionalInequalities.Energy
open FunctionalInequalities FunctionalInequalities.Energy
universe u
section Reduction
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
namespace FunctionalInequalities.Energy
end FunctionalInequalities.Energy
open FunctionalInequalities.Energy in
omit [InnerProductSpace ℝ V] in
/-- the local Lipschitz product rule.  A locally Lipschitz function times a bounded globally Lipschitz one is locally
Lipschitz. -/
theorem solution {g h : V → ℝ} {N : ℝ≥0} (hg : LocallyLipschitz g)
    (hh : LipschitzWith N h) (hh1 : ∀ x, |h x| ≤ 1) :
    LocallyLipschitz (fun x ↦ g x * h x) := by
  intro x
  obtain ⟨K, t, ht, hK⟩ := hg x
  obtain ⟨r, hr, hrt⟩ := Metric.mem_nhds_iff.mp ht
  set s : Set V := Metric.ball x (min r 1) with hs
  have hsub : s ⊆ t := (Metric.ball_subset_ball (min_le_left _ _)).trans hrt
  have hxs : x ∈ s := Metric.mem_ball_self (lt_min hr one_pos)
  have hKs : LipschitzOnWith K g s := hK.mono hsub
  have hbound : ∀ y ∈ s, |g y| ≤ |g x| + K := by
    intro y hy
    have : dist (g y) (g x) ≤ K * dist y x := hKs.dist_le_mul y hy x hxs
    have hd : dist y x < 1 := lt_of_lt_of_le (by simpa [hs, Metric.mem_ball] using hy)
      (min_le_right _ _)
    have : |g y - g x| ≤ K * dist y x := by simpa [Real.dist_eq] using this
    have h2 : |g y| ≤ |g x| + K * dist y x := by
      have := abs_sub_abs_le_abs_sub (g y) (g x)
      linarith [abs_nonneg (g x)]
    refine h2.trans ?_
    have : K * dist y x ≤ K * 1 := by
      exact mul_le_mul_of_nonneg_left hd.le K.coe_nonneg
    linarith
  refine ⟨(K + (|g x| + K) * N).toNNReal, s, Metric.isOpen_ball.mem_nhds hxs, ?_⟩
  refine LipschitzOnWith.of_dist_le_mul fun y hy z hz ↦ ?_
  have hCnn : (0 : ℝ) ≤ K + (|g x| + K) * N := by positivity
  rw [Real.coe_toNNReal _ hCnn]
  have hgyz : |g y - g z| ≤ K * dist y z := by
    simpa [Real.dist_eq] using hKs.dist_le_mul y hy z hz
  have hhyz : |h y - h z| ≤ N * dist y z := by
    simpa [Real.dist_eq] using hh.dist_le_mul y z
  have hkey : g y * h y - g z * h z = (g y - g z) * h y + g z * (h y - h z) := by ring
  have h1 : |(g y - g z) * h y| ≤ K * dist y z := by
    rw [abs_mul]
    calc |g y - g z| * |h y| ≤ (K * dist y z) * 1 := by
          apply mul_le_mul hgyz (hh1 y) (abs_nonneg _)
          positivity
      _ = K * dist y z := by ring
  have h2 : |g z * (h y - h z)| ≤ (|g x| + K) * (N * dist y z) := by
    rw [abs_mul]
    exact mul_le_mul (hbound z hz) hhyz (abs_nonneg _) (by positivity)
  calc dist (g y * h y) (g z * h z) = |(g y - g z) * h y + g z * (h y - h z)| := by
        rw [Real.dist_eq, hkey]
    _ ≤ |(g y - g z) * h y| + |g z * (h y - h z)| := abs_add_le _ _
    _ ≤ K * dist y z + (|g x| + K) * (N * dist y z) := add_le_add h1 h2
    _ = (K + (|g x| + K) * N) * dist y z := by ring
