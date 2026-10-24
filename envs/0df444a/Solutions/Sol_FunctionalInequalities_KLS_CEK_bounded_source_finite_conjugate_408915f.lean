-- Prove2me | solution 1 for FunctionalInequalities.KLS.CEK.bounded_source_finite_conjugate_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T15:49:10.137091+00:00
-- url     : https://prove2.me/submissions/5ba30c4f-4d8c-49f0-b32b-f80a19e5c366

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
import Theorems.Thm_FunctionalInequalities_Analysis_convex_epigraph_legendre_408915f
import Theorems.Thm_FunctionalInequalities_Analysis_exists_real_global_minimum_of_bounded_domain_408915f
import Theorems.Thm_FunctionalInequalities_Analysis_legendre_le_of_real_lower_bound_408915f
import Theorems.Thm_FunctionalInequalities_Analysis_legendre_ne_bot_iff_408915f
import Theorems.Thm_FunctionalInequalities_KLS_CEK_bounded_source_cap_lsc_408915f

section
noncomputable section
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
/-- Conjugation produces a convex potential from precisely a nonempty effective
domain, without any convexity or lower-semicontinuity premise on the primal. -/
theorem FunctionalInequalities.Analysis.convexPotential_legendre (φ : E → EReal) (hfinite : ∃ x, φ x ≠ ⊤) :
    ConvexPotential (legendre φ) :=
  ⟨fun y => (legendre_ne_bot_iff_408915f φ y).mpr hfinite, convex_epigraph_legendre_408915f φ⟩
end
end
end
end

section
noncomputable section
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Probability
end FunctionalInequalities.Probability
open FunctionalInequalities FunctionalInequalities.Probability
section
namespace FunctionalInequalities.Probability.MomentMeasure
end FunctionalInequalities.Probability.MomentMeasure
open FunctionalInequalities FunctionalInequalities.Probability FunctionalInequalities.Probability.MomentMeasure
open FunctionalInequalities.Analysis
section
open MeasureTheory
open scoped ENNReal
section Truncation
variable {E : Type*} [MeasurableSpace E] {μ : Measure E}
/-- A nonzero measure and the source a.e. finiteness give a real finite-domain
witness; probability normalization and centering are unnecessary. -/
theorem FunctionalInequalities.Probability.MomentMeasure.potentialIntegrable_exists_finite (f : E → EReal) (hμ : μ ≠ 0)
    (hf : PotentialIntegrable f μ) : ∃ x, f x ≠ ⊤ := by
  let : NeZero μ := ⟨hμ⟩
  exact hf.2.1.exists
end Truncation
end
end
end
end
end
end

section
noncomputable section
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
open MeasureTheory Set Metric
open scoped ENNReal Topology RealInnerProductSpace
open FunctionalInequalities
open FunctionalInequalities.Analysis
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Properness excludes bottom for the actual conjugate, and the bounded-slope
upper bound excludes top. No conversion of an infinite value is used. -/
theorem FunctionalInequalities.Analysis.legendre_finite_of_bounded_domain
    (φ : E → EReal) (L : NNReal) (m : ℝ)
    (hbot : ∀ y, φ y ≠ ⊥)
    (hfinite : ∃ y, φ y ≠ ⊤)
    (hdom : ∀ y, φ y ≠ ⊤ → y ∈ closedBall (0 : E) (L : ℝ))
    (hfloor : ∀ y, (m : EReal) ≤ φ y) :
    ∀ x, legendre φ x ≠ ⊤ ∧ legendre φ x ≠ ⊥ := by
  intro x
  refine ⟨?_, (convexPotential_legendre φ hfinite).1 x⟩
  intro htop
  have hu := legendre_le_of_real_lower_bound_408915f φ L m hbot hdom hfloor x
  rw [htop] at hu
  exact (not_le_of_gt (EReal.coe_lt_top ((L : ℝ) * ‖x‖ - m))) hu
end
end
end
end

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
/-- Source-derived compact minimum and globally finite actual conjugate.
The only source inputs are the bundled isotropic probability and its AE norm
bound. The real primal is defined after global finiteness has been established.
This endpoint does not yet assert real convexity, Lipschitz continuity, or the
Bochner exponential-integrability and probability-law bridge. -/
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
      ∀ f : E → EReal, FunctionalInequalities.Probability.MomentMeasure.PotentialIntegrable f (μ : Measure E) →
        FunctionalInequalities.Probability.MomentMeasure.variationalFunctional (volume : Measure E) (μ : Measure E) f ≤
          FunctionalInequalities.Probability.MomentMeasure.variationalFunctional (volume : Measure E) (μ : Measure E) q := by
  classical
  obtain ⟨q, hqconv, hqlsc, hqpot, hqdom, hqmass, hqmax⟩ :=
    FunctionalInequalities.KLS.CEK.bounded_source_cap_lsc_408915f μ hμ L hL
  have hμne : (μ : Measure E) ≠ 0 := by
    intro hzero
    have hprob : (μ : Measure E) univ = 1 := measure_univ
    rw [hzero] at hprob
    simp at hprob
  have hqfinite : ∃ y, q y ≠ ⊤ :=
    FunctionalInequalities.Probability.MomentMeasure.potentialIntegrable_exists_finite q hμne hqpot
  obtain ⟨a, haB, m, ham, hfloor⟩ :=
    FunctionalInequalities.Analysis.exists_real_global_minimum_of_bounded_domain_408915f
      q L hqpot.1 hqfinite hqlsc hqdom
  have hfinite : ∀ x, FunctionalInequalities.Analysis.legendre q x ≠ ⊤ ∧ FunctionalInequalities.Analysis.legendre q x ≠ ⊥ :=
    FunctionalInequalities.Analysis.legendre_finite_of_bounded_domain q L m hqpot.1 hqfinite hqdom hfloor
  let ψ : E → ℝ := fun x => (FunctionalInequalities.Analysis.legendre q x).toReal
  have hψ : ∀ x, FunctionalInequalities.Analysis.legendre q x = (ψ x : EReal) := by
    intro x
    exact (EReal.coe_toReal (hfinite x).1 (hfinite x).2).symm
  refine ⟨q, a, m, ψ, hqconv, hqlsc, hqpot, hqdom, haB, ham, hfloor,
    hfinite, ?_, rfl, hψ, hqmass, hqmax⟩
  intro x
  exact FunctionalInequalities.Analysis.legendre_le_of_real_lower_bound_408915f q L m hqpot.1 hqdom hfloor x
