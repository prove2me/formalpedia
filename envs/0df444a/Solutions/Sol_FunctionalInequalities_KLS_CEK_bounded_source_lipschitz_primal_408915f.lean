-- Prove2me | solution 1 for FunctionalInequalities.KLS.CEK.bounded_source_lipschitz_primal_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T15:50:23.987139+00:00
-- url     : https://prove2.me/submissions/a0dd43be-8d6d-41f7-8511-f02047a4b7d8

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Bochner_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Gamma
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Laplacian
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Affine
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_AffineMaximum
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_BoundedConjugate
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Legendre
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_RadialExtension
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Cutoff_SmoothBall
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Lipschitz_Gradient
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_Isotropic
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_AffineSupport
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Covariance_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_MomentMeasure_Basic
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Norm
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Mathlib.Analysis.Normed.Affine.Convex
import Mathlib.Analysis.Normed.Affine.Isometry
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.EReal.Operations
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Probability.Moments.CovarianceBilin
import Mathlib.Tactic.NoncommRing
import Mathlib.Topology.Bases
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.MetricSpace.Sequences
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Sequences
import Theorems.Thm_FunctionalInequalities_Analysis_lipschitzWith_real_legendre_408915f
import Theorems.Thm_FunctionalInequalities_Analysis_real_convexOn_legendre_408915f
import Theorems.Thm_FunctionalInequalities_KLS_CEK_bounded_source_finite_conjugate_408915f
import Theorems.Thm_FunctionalInequalities_Probability_MomentMeasure_real_legendre_normalization_408915f

noncomputable section
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.KLS
end FunctionalInequalities.KLS
open FunctionalInequalities FunctionalInequalities.KLS
section
namespace FunctionalInequalities.KLS.CEK
end FunctionalInequalities.KLS.CEK
open FunctionalInequalities FunctionalInequalities.KLS FunctionalInequalities.KLS.CEK
open MeasureTheory Set Metric
open scoped ENNReal Topology RealInnerProductSpace
open FunctionalInequalities
open FunctionalInequalities.Analysis
open FunctionalInequalities.KLS
open FunctionalInequalities.Probability
open FunctionalInequalities.Probability.MomentMeasure
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
namespace FunctionalInequalities.KLS.CEK
end FunctionalInequalities.KLS.CEK
open FunctionalInequalities.KLS.CEK in
/-- Weak source-law-linked normalized primal. Every new conclusion is derived
from `bounded_source_finite_conjugate` for this actual bounded isotropic source.
No convexity, Lipschitz, integrability, normalization, or optimizer premise is
added to the source interface. The original finite-conjugate data are retained. -/
theorem solution
    (μ : ProbabilityMeasure E) (hμ : FunctionalInequalities.KLS.Isotropic μ) (L : NNReal)
    (hL : ∀ᵐ y ∂(μ : Measure E), ‖y‖ ≤ (L : ℝ)) :
    ∃ (q : E → EReal) (a : E) (m : ℝ) (ψ : E → ℝ),
      FunctionalInequalities.Analysis.ConvexPotential q ∧
      LowerSemicontinuous q ∧
      FunctionalInequalities.Probability.MomentMeasure.PotentialIntegrable q (μ : Measure E) ∧
      (∀ y, q y ≠ ⊤ → y ∈ closedBall (0 : E) (L : ℝ)) ∧
      a ∈ closedBall (0 : E) (L : ℝ) ∧
      q a = (m : EReal) ∧
      (∀ y, (m : EReal) ≤ q y) ∧
      (∀ x, FunctionalInequalities.Analysis.legendre q x ≠ ⊤ ∧ FunctionalInequalities.Analysis.legendre q x ≠ ⊥) ∧
      (∀ x, FunctionalInequalities.Analysis.legendre q x ≤ (((L : ℝ) * ‖x‖ - m : ℝ) : EReal)) ∧
      ψ = (fun x => (FunctionalInequalities.Analysis.legendre q x).toReal) ∧
      (∀ x, FunctionalInequalities.Analysis.legendre q x = (ψ x : EReal)) ∧
      FunctionalInequalities.Probability.MomentMeasure.mass (volume : Measure E) (FunctionalInequalities.Analysis.legendre q) = 1 ∧
      ConvexOn ℝ (univ : Set E) ψ ∧
      LipschitzWith L ψ ∧
      Continuous ψ ∧
      Integrable (fun x => Real.exp (-ψ x)) (volume : Measure E) ∧
      (∫ x, Real.exp (-ψ x) ∂(volume : Measure E)) = 1 ∧
      IsProbabilityMeasure
        (FunctionalInequalities.Probability.MomentMeasure.weightedMeasure (volume : Measure E) (fun x => (ψ x : EReal))) ∧
      ∀ f : E → EReal, FunctionalInequalities.Probability.MomentMeasure.PotentialIntegrable f (μ : Measure E) →
        FunctionalInequalities.Probability.MomentMeasure.variationalFunctional (volume : Measure E) (μ : Measure E) f ≤
          FunctionalInequalities.Probability.MomentMeasure.variationalFunctional (volume : Measure E) (μ : Measure E) q := by
  obtain ⟨q, a, m, ψ, hqconv, hqlsc, hqpot, hqdom, haB, ham, hfloor,
    hfinite, hupper, hdef, hψ, hqmass, hqmax⟩ :=
    FunctionalInequalities.KLS.CEK.bounded_source_finite_conjugate_408915f μ hμ L hL
  have hconv : ConvexOn ℝ (univ : Set E) ψ :=
    FunctionalInequalities.Analysis.real_convexOn_legendre_408915f q ψ hψ
  have hlip : LipschitzWith L ψ :=
    FunctionalInequalities.Analysis.lipschitzWith_real_legendre_408915f q L ψ hqpot.1 hqdom hψ
  obtain ⟨hexp, hint, hprob⟩ :=
    FunctionalInequalities.Probability.MomentMeasure.real_legendre_normalization_408915f (volume : Measure E) q ψ hψ hqmass
  exact ⟨q, a, m, ψ, hqconv, hqlsc, hqpot, hqdom, haB, ham, hfloor,
    hfinite, hupper, hdef, hψ, hqmass, hconv, hlip, hlip.continuous,
    hexp, hint, hprob, hqmax⟩
