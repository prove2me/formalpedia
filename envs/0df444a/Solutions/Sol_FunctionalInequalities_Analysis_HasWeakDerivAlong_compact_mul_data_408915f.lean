-- Prove2me | solution 1 for FunctionalInequalities.Analysis.HasWeakDerivAlong.compact_mul_data_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T14:55:13.014895+00:00
-- url     : https://prove2.me/submissions/00cfa840-5efd-4e6c-8378-e6c9e3a58895

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
import Theorems.Thm_FunctionalInequalities_Analysis_HasWeakDerivAlong_mul_contDiff_408915f
import Theorems.Thm_FunctionalInequalities_Analysis_memLp_mul_of_hasCompactSupport_408915f

noncomputable section
open MeasureTheory
open scoped ContDiff
universe u
section SharedCompactLocalTools
open MeasureTheory Set Filter
open scoped ContDiff RealInnerProductSpace Topology
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
namespace FunctionalInequalities.Analysis.HasWeakDerivAlong
end FunctionalInequalities.Analysis.HasWeakDerivAlong
open FunctionalInequalities.Analysis.HasWeakDerivAlong in
/-- Multiplying a weak derivative pair `(f, df)` along `v` by a compactly supported C1 function `ψ`, with `df` L2 and
`f` essentially bounded on compact sets, gives the weak derivative of `ψ f`, compact supports and a globally L2 derivative. -/
theorem solution {n : ℕ}
    {f df : EuclideanSpace ℝ (Fin n) → ℝ} {v : EuclideanSpace ℝ (Fin n)}
    (h : FunctionalInequalities.Analysis.HasWeakDerivAlong f df v)
    (hdf : ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
      MemLp df 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S))
    (hf : ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
      MemLp f (⊤ : ENNReal) ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S))
    {ψ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hψ : ContDiff ℝ 1 ψ) (hψc : HasCompactSupport ψ) :
    FunctionalInequalities.Analysis.HasWeakDerivAlong (fun x => ψ x * f x)
      (fun x => ψ x * df x + fderiv ℝ ψ x v * f x) v ∧
    HasCompactSupport (fun x => ψ x * f x) ∧
    HasCompactSupport (fun x => ψ x * df x + fderiv ℝ ψ x v * f x) ∧
    MemLp (fun x => ψ x * df x + fderiv ℝ ψ x v * f x) 2
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
  have hdψ : Continuous (fun x => fderiv ℝ ψ x v) :=
    (hψ.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hdψc : HasCompactSupport (fun x => fderiv ℝ ψ x v) :=
    hψc.fderiv_apply ℝ v
  have hf2 : ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
      MemLp f 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) := by
    intro S hS
    let : IsFiniteMeasure ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) :=
      isFiniteMeasure_restrict.mpr hS.measure_lt_top.ne
    exact (hf S hS).mono_exponent le_top
  refine ⟨h.mul_contDiff_408915f hψ hψc, hψc.mul_right, ?_, ?_⟩
  · exact hψc.mul_right.add hdψc.mul_right
  · exact (FunctionalInequalities.Analysis.memLp_mul_of_hasCompactSupport_408915f hψ.continuous hψc hdf).add (FunctionalInequalities.Analysis.memLp_mul_of_hasCompactSupport_408915f hdψ hdψc hf2)
