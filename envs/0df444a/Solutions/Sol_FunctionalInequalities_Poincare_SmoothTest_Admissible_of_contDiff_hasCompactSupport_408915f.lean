-- Prove2me | solution 1 for FunctionalInequalities.Poincare.SmoothTest.Admissible.of_contDiff_hasCompactSupport_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T17:41:42.414578+00:00
-- url     : https://prove2.me/submissions/f9f57676-cb88-4c98-b85b-1364cbcb3862

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Cutoff_SmoothBall
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Lipschitz_Gradient
import Definitions.Def_KLS408915f_FunctionalInequalities_Poincare_SmoothTest_Basic
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.FDeriv.Norm
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Probability.Moments.Variance
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.Topology.MetricSpace.Lipschitz

noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ContDiff
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Poincare
end FunctionalInequalities.Poincare
open FunctionalInequalities FunctionalInequalities.Poincare
section
namespace FunctionalInequalities.Poincare.SmoothTest
end FunctionalInequalities.Poincare.SmoothTest
open FunctionalInequalities FunctionalInequalities.Poincare FunctionalInequalities.Poincare.SmoothTest
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E]
section Cutoff
variable [FiniteDimensional ℝ E]
namespace FunctionalInequalities.Poincare.SmoothTest.Admissible
end FunctionalInequalities.Poincare.SmoothTest.Admissible
open FunctionalInequalities.Poincare.SmoothTest.Admissible in
/-- A `C^∞` function with compact support is an admissible test for every finite measure. -/
theorem solution {μ : Measure E} [IsFiniteMeasure μ]
    {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) : FunctionalInequalities.Poincare.SmoothTest.Admissible μ f := by
    refine
      { smooth' := hf
        memLp_two := ?_
        energy_integrable := ?_ }
    · obtain ⟨C, hC⟩ := hc.exists_bound_of_continuous hf.continuous
      exact
        MemLp.of_bound hf.continuous.aestronglyMeasurable C
          (Filter.Eventually.of_forall hC)
    · have hgrad : Continuous (gradient f) := by
        change
          Continuous
            (fun x => (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ f x))
        exact
          (InnerProductSpace.toDual ℝ E).symm.continuous.comp
            (hf.continuous_fderiv (by simp))
      have henergy : Continuous (fun x => ‖gradient f x‖ ^ 2) :=
        hgrad.norm.pow 2
      have hfd : HasCompactSupport (fun x => fderiv ℝ f x) :=
        hc.fderiv ℝ
      have hsub :
          Function.support (fun x => ‖gradient f x‖ ^ 2) ⊆
            Function.support (fun x => fderiv ℝ f x) := by
        intro x hx hfx
        apply hx
        simp [gradient, hfx]
      exact henergy.integrable_of_hasCompactSupport (hfd.mono hsub)
