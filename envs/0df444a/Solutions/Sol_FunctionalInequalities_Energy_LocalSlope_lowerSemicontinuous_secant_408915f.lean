-- Prove2me | solution 1 for FunctionalInequalities.Energy.LocalSlope.lowerSemicontinuous_secant_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T15:52:32.421735+00:00
-- url     : https://prove2.me/submissions/62743d23-ee37-47c3-9267-42f81329df42

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
section
namespace FunctionalInequalities.Energy.LocalSlope
end FunctionalInequalities.Energy.LocalSlope
open FunctionalInequalities FunctionalInequalities.Energy FunctionalInequalities.Energy.LocalSlope
section Measurability
variable {X : Type*} [MetricSpace X]
namespace FunctionalInequalities.Energy.LocalSlope
end FunctionalInequalities.Energy.LocalSlope
open FunctionalInequalities.Energy.LocalSlope in
/-- Each secant supremum of a continuous function is lower semicontinuous. -/
theorem solution {f : X → ℝ} (hf : Continuous f) (r : ℝ) :
    LowerSemicontinuous (FunctionalInequalities.Energy.LocalSlope.secant f r) := by
  intro x t ht
  have ht' : t < ⨆ (y : X) (_ : dist y x < r), ENNReal.ofReal (dist (f y) (f x) / dist y x) := ht
  obtain ⟨y, hy⟩ := lt_iSup_iff.1 ht'
  obtain ⟨hyr, hyt⟩ := lt_iSup_iff.1 hy
  have hpos : 0 < dist y x := by
    rcases eq_or_lt_of_le (dist_nonneg (x := y) (y := x)) with h0 | h0
    · exfalso
      rw [← h0] at hyt
      simp at hyt
    · exact h0
  set q : X → ℝ := fun x' ↦ dist (f y) (f x') / dist y x' with hq
  have hcont : ContinuousAt (fun x' ↦ ENNReal.ofReal (q x')) x := by
    refine ENNReal.continuous_ofReal.continuousAt.comp ?_
    refine ContinuousAt.div ?_ ?_ hpos.ne'
    · exact (continuous_const.dist hf).continuousAt
    · exact (continuous_const.dist continuous_id).continuousAt
  have hball : ∀ᶠ x' in 𝓝 x, dist y x' < r := by
    have hmem : Metric.ball y r ∈ 𝓝 x :=
      Metric.isOpen_ball.mem_nhds (by simpa [Metric.mem_ball, dist_comm] using hyr)
    filter_upwards [hmem] with x' hx'
    simpa [Metric.mem_ball, dist_comm] using hx'
  have hgt : ∀ᶠ x' in 𝓝 x, t < ENNReal.ofReal (q x') := hcont (lt_mem_nhds hyt)
  filter_upwards [hball, hgt] with x' h1 h2
  refine lt_of_lt_of_le h2 ?_
  rw [FunctionalInequalities.Energy.LocalSlope.secant]
  exact le_iSup₂_of_le y h1 le_rfl
