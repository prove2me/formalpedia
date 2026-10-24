-- Prove2me | solution 1 for FunctionalInequalities.Analysis.compact_bounded_test_domination_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T15:06:40.893297+00:00
-- url     : https://prove2.me/submissions/d8eefc75-f66a-4a59-bfaf-dec7cafb6f6d

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Cutoff_SmoothBall
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Lipschitz_Gradient
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_WeakDerivative_Basic
import Mathlib
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Norm
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.SpecificCodomains.Pi
import Mathlib.Topology.MetricSpace.Lipschitz

noncomputable section
open MeasureTheory
open scoped ContDiff
universe u
section BoundedWeakDerivativeTesting
open MeasureTheory Filter Set
open scoped Topology ContDiff
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities.Analysis in
/-- A compact-local L1 density admits a common integrable bound for rough bounded tests. -/
theorem solution {n : ℕ}
    {F η : EuclideanSpace ℝ (Fin n) → ℝ} {S : Set (EuclideanSpace ℝ (Fin n))}
    {C : ℝ} (hF : LocallyIntegrable F (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hS : IsCompact S)
    (hη : AEStronglyMeasurable η (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hsupp : Function.support η ⊆ S) (hbound : ∀ x, ‖η x‖ ≤ C) :
    Integrable (S.indicator fun x => C * ‖F x‖)
        (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
      (∀ x, ‖F x * η x‖ ≤ (S.indicator fun y => C * ‖F y‖) x) ∧
      Integrable (fun x => F x * η x)
        (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
  have hb : Integrable (S.indicator fun x => C * ‖F x‖)
      (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    (integrable_indicator_iff hS.measurableSet).2
      ((hF.integrableOn_isCompact hS).norm.const_mul C)
  have hprod (x : EuclideanSpace ℝ (Fin n)) :
      ‖F x * η x‖ ≤ (S.indicator fun y => C * ‖F y‖) x := by
    by_cases hx : x ∈ S
    · rw [Set.indicator_of_mem hx, norm_mul]
      calc
        ‖F x‖ * ‖η x‖ ≤ ‖F x‖ * C :=
          mul_le_mul_of_nonneg_left (hbound x) (norm_nonneg _)
        _ = C * ‖F x‖ := mul_comm _ _
    · have hzero : η x = 0 := by
        by_contra hne
        exact hx (hsupp hne)
      rw [Set.indicator_of_notMem hx, hzero, mul_zero, norm_zero]
  exact ⟨hb, hprod, hb.mono' (hF.aestronglyMeasurable.mul hη)
    (Filter.Eventually.of_forall hprod)⟩
