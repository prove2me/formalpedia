-- Prove2me | solution 1 for FunctionalInequalities.Analysis.memLp_mul_of_hasCompactSupport_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T14:53:36.471275+00:00
-- url     : https://prove2.me/submissions/d007b43d-48e8-42d9-b4d4-75607bdb191b

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
section WeakProducts
open MeasureTheory Filter Set Metric InnerProductSpace
open scoped Convolution ContDiff ENNReal RealInnerProductSpace Topology
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
/-- A continuous compactly supported cutoff times a function that is L2 on every compact set is globally L2. -/
theorem solution {n : ℕ}
    {f χ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hχ : Continuous χ) (hχc : HasCompactSupport χ)
    (hf : ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
      MemLp f 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) :
    MemLp (fun x => χ x * f x) 2
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
  classical
  have hKm : MeasurableSet (tsupport χ) := (isClosed_tsupport χ).measurableSet
  have hind : MemLp ((tsupport χ).indicator f) 2
      (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    (memLp_indicator_iff_restrict hKm).mpr (hf (tsupport χ) hχc)
  have hχlp : MemLp χ (⊤ : ENNReal) (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    hχ.memLp_of_hasCompactSupport hχc
  have hm : MemLp (fun x => χ x * ((tsupport χ).indicator f) x) 2
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := hind.mul' hχlp
  convert hm using 1
  funext x
  by_cases hx : x ∈ tsupport χ
  · rw [Set.indicator_of_mem hx]
  · rw [Set.indicator_of_notMem hx, image_eq_zero_of_notMem_tsupport hx,
      zero_mul, zero_mul]
