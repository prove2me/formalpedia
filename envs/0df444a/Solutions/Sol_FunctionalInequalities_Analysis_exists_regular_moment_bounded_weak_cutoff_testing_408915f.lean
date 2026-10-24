-- Prove2me | solution 1 for FunctionalInequalities.Analysis.exists_regular_moment_bounded_weak_cutoff_testing_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T16:10:40.555993+00:00
-- url     : https://prove2.me/submissions/2f456d19-0d27-4a3c-9187-7d0403554382

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Bochner_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Gamma
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_HessianOperator
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_InverseHessian_Weak
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Laplacian
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_MongeAmpere
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_WeakHessian
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Affine
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_AffineMaximum
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Alexandrov
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_BoundedConjugate
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Caffarelli
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Legendre
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Normalization
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Proximal
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_RadialExtension
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Subgradient
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Viscosity
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Cutoff_LipschitzBall
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Cutoff_SmoothBall
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Lipschitz_Gradient
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Matrix_DeterminantDerivative
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Matrix_Piola
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Matrix_Positivity
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Operator_Coordinates
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_WeakDerivative_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_Isotropic
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_AffineSupport
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_BrunnMinkowski
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Covariance_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Line_BrunnMinkowski
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_MomentMeasure_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Stein_Kernel
import Mathlib
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.DerivativeTest
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Norm
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Calculus.TaylorIntegral
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Extrema
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.Measure
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.InnerProductSpace.NormDet
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Mathlib.Analysis.Normed.Affine.Convex
import Mathlib.Analysis.Normed.Affine.Isometry
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Star
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.SpecificCodomains.Pi
import Mathlib.MeasureTheory.SpecificCodomains.WithLp
import Mathlib.Probability.Moments.CovarianceBilin
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Algebra.Group.Matrix
import Mathlib.Topology.Algebra.MetricSpace.Lipschitz
import Mathlib.Topology.Algebra.Support
import Mathlib.Topology.Bases
import Mathlib.Topology.EMetricSpace.Lipschitz
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.MetricSpace.Sequences
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Sequences
import Theorems.Thm_FunctionalInequalities_Analysis_exists_regular_moment_weak_cutoffs_408915f
import Theorems.Thm_FunctionalInequalities_Analysis_integral_rough_mul_generator_eq_neg_energy_of_contDiff_one_408915f

section
noncomputable section
open MeasureTheory
open scoped ContDiff RealInnerProductSpace
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
section
namespace FunctionalInequalities.Analysis.BakryEmery
end FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities FunctionalInequalities.Analysis FunctionalInequalities.Analysis.BakryEmery
/-- A unit normalisation `∫ e^{−φ} = 1` forces integrability of `e^{−φ}`. -/
theorem FunctionalInequalities.Analysis.BakryEmery.integrable_exp_neg_of_integral_eq_one {α : Type*} [MeasurableSpace α] (m : Measure α)
    (φ : α → ℝ) (hnorm : ∫ x, Real.exp (-φ x) ∂m = 1) :
    Integrable (fun x => Real.exp (-φ x)) m := by
  by_contra hh
  rw [integral_undef hh] at hnorm
  norm_num at hnorm
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
end
end
end
end
end

section RegularSource
open MeasureTheory Set
open scoped ContDiff
variable {n : ℕ} (hn : 0 < n)
    {K : Set (EuclideanSpace ℝ (Fin n))} {W : EuclideanSpace ℝ (Fin n) → ℝ}
    {κ : ℝ} (hκ : 0 < κ) (hK : IsCompact K) (hKc : Convex ℝ K)
    (hKint : (interior K).Nonempty) (hW : ContDiff ℝ ∞ W)
    (hstrong : ConvexOn ℝ univ (fun y => W y - (κ / 2) * ‖y‖ ^ 2))
    (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
    (hμ : (μ : Measure (EuclideanSpace ℝ (Fin n))) =
      (volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
        (K.indicator fun p => ENNReal.ofReal (Real.exp (-W p))))
    (hiso : FunctionalInequalities.KLS.Isotropic μ)
noncomputable section
open MeasureTheory Set Filter
open scoped RealInnerProductSpace ContDiff Topology
open FunctionalInequalities.Probability.Stein
section RegularMomentBoundedWeakCutoffTesting
open MeasureTheory Filter Set Metric Matrix
open FunctionalInequalities.Probability.Stein
open scoped ContDiff Topology RealInnerProductSpace
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
include hn hκ hK hKc hKint hW hstrong hμ hiso in
/-- At the same regular moment witness `u`, `L`, `LF`, `T` and common cutoff family as
`exists_regular_moment_weak_cutoffs` (whole payload retained), every globally bounded locally integrable weak `η`
with compact-local L2 coordinate derivatives satisfies the rough inverse-Hessian cutoff-generator identity for all `r ≥ 1`. -/
theorem solution :
    ∃ (u : EuclideanSpace ℝ (Fin n) → ℝ) (L LF : NNReal)
        (T : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → Fin n → ℝ),
      (ConvexOn ℝ univ u ∧ LipschitzWith L u ∧
      (∫ x, Real.exp (-u x) ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) = 1 ∧
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)).map (gradient u) =
        (μ : Measure (EuclideanSpace ℝ (Fin n))) ∧
      ContDiff ℝ 1 u ∧ LipschitzWith (Real.toNNReal (16 / κ)) (gradient u) ∧
      LipschitzWith LF (fun x => -u x + W (gradient u x)) ∧
      (∀ x h, u (x + h) + u (x - h) - 2 * u x ≤ (4 / κ) * ‖h‖ ^ 2) ∧
      (∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
        (FunctionalInequalities.Probability.Stein.hessianMatrix u x).PosDef ∧
        Real.log (FunctionalInequalities.Probability.Stein.hessianMatrix u x).det = -u x + W (gradient u x) ∧
        ((16 / κ) • (1 : Matrix (Fin n) (Fin n) ℝ) - FunctionalInequalities.Probability.Stein.hessianMatrix u x).PosSemidef) ∧
      (∀ k i j,
        FunctionalInequalities.Analysis.HasWeakDerivAlong (fun x => FunctionalInequalities.Probability.Stein.hessianMatrix u x i j) (fun x => T x k i j)
            (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
          ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
            MemLp (fun x => T x k i j) 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
      (∃ LE : NNReal,
        LipschitzWith LE (fun x => Real.exp (-u x + W (gradient u x)))) ∧
      (∀ k : Fin n,
        FunctionalInequalities.Analysis.HasWeakDerivAlong (fun x => (FunctionalInequalities.Probability.Stein.hessianMatrix u x).det)
          (fun x => (FunctionalInequalities.Probability.Stein.hessianMatrix u x).det *
            ((FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹ * (Matrix.of fun i j => T x k i j)).trace)
          (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
        (∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
          MemLp (fun x => (FunctionalInequalities.Probability.Stein.hessianMatrix u x).det *
            ((FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹ * (Matrix.of fun i j => T x k i j)).trace)
            2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
        FunctionalInequalities.Analysis.HasWeakDerivAlong (fun x => Real.log (FunctionalInequalities.Probability.Stein.hessianMatrix u x).det)
          (fun x => ((FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹ * (Matrix.of fun i j => T x k i j)).trace)
          (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
        (∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
          ((FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹ * (Matrix.of fun i j => T x k i j)).trace =
            fderiv ℝ (fun y => -u y + W (gradient u y)) x
              (EuclideanSpace.basisFun (Fin n) ℝ k)) ∧
        (∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
          ((FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹ * (Matrix.of fun i j => T x k i j)).trace =
            -fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ k) +
              ∑ a : Fin n, FunctionalInequalities.Probability.Stein.hessianMatrix u x k a *
                fderiv ℝ W (gradient u x) (EuclideanSpace.basisFun (Fin n) ℝ a))) ∧
      (∀ k i j : Fin n,
        FunctionalInequalities.Analysis.HasWeakDerivAlong (fun x => (FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹ i j)
          (fun x => -(((FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹ *
            (Matrix.of fun a b => T x k a b) * (FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹) i j))
          (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
        (∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
          MemLp (fun x => -(((FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹ *
            (Matrix.of fun a b => T x k a b) * (FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹) i j)) 2
            ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
        ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
          MemLp (fun x => (FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹ i j) (⊤ : ENNReal)
            ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
      (∀ i j : Fin n,
        Integrable (fun x => FunctionalInequalities.Probability.Stein.hessianMatrix u x i j)
          ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)) ∧
        (∫ x, FunctionalInequalities.Probability.Stein.hessianMatrix u x i j
          ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u))) =
          (1 : Matrix (Fin n) (Fin n) ℝ) i j) ∧
      (∀ i j : Fin n,
      FunctionalInequalities.Analysis.HasWeakDerivAlong
        (fun x => ((FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹ * (Matrix.of fun a b => T x i a b)).trace)
        (fun x => -FunctionalInequalities.Probability.Stein.hessianMatrix u x j i +
          ∑ a : Fin n,
            (T x j i a * fderiv ℝ W (gradient u x)
              (EuclideanSpace.basisFun (Fin n) ℝ a) +
            FunctionalInequalities.Probability.Stein.hessianMatrix u x i a *
              ∑ b : Fin n, FunctionalInequalities.Probability.Stein.hessianMatrix u x j b * FunctionalInequalities.Probability.Stein.hessianMatrix W (gradient u x) b a))
        (EuclideanSpace.basisFun (Fin n) ℝ j) ∧
      ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
        MemLp
          (fun x => -FunctionalInequalities.Probability.Stein.hessianMatrix u x j i +
            ∑ a : Fin n,
              (T x j i a * fderiv ℝ W (gradient u x)
                (EuclideanSpace.basisFun (Fin n) ℝ a) +
              FunctionalInequalities.Probability.Stein.hessianMatrix u x i a *
                ∑ b : Fin n, FunctionalInequalities.Probability.Stein.hessianMatrix u x j b * FunctionalInequalities.Probability.Stein.hessianMatrix W (gradient u x) b a))
          2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
    (let Q := fun x i j => -FunctionalInequalities.Probability.Stein.hessianMatrix u x j i +
          ∑ a : Fin n,
            (T x j i a * fderiv ℝ W (gradient u x)
              (EuclideanSpace.basisFun (Fin n) ℝ a) +
            FunctionalInequalities.Probability.Stein.hessianMatrix u x i a *
              ∑ b : Fin n, FunctionalInequalities.Probability.Stein.hessianMatrix u x j b * FunctionalInequalities.Probability.Stein.hessianMatrix W (gradient u x) b a)
    let R := fun x => (FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹
    let D := fun x k b a => -((R x * (Matrix.of fun c d => T x k c d) * R x) b a)
    let J := fun x i j a => ∑ b : Fin n, R x b a * T x b i j
    let C := fun x i j => Q x i j -
      (∑ a : Fin n, ∑ b : Fin n, T x i a b * D x j b a) +
      ∑ b : Fin n, T x b i j * (∑ a : Fin n, D x a b a)
    ∀ i j : Fin n,
      (∀ a : Fin n, ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
        MemLp (fun x => J x i j a) 2
          ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
      LocallyIntegrable (fun x => C x i j)
        (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
      ∀ ψ : EuclideanSpace ℝ (Fin n) → ℝ,
        ContDiff ℝ 1 ψ → HasCompactSupport ψ →
        (∫ x, ∑ a : Fin n, J x i j a *
          fderiv ℝ ψ x (EuclideanSpace.basisFun (Fin n) ℝ a)
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
        -(∫ x, C x i j * ψ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))) ∧
  (    let R := fun x => (FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹
    let J := fun x i j a => ∑ b : Fin n, R x b a * T x b i j
    let E := fun x i j => -FunctionalInequalities.Probability.Stein.hessianMatrix u x i j +
      (FunctionalInequalities.Probability.Stein.hessianMatrix u x * FunctionalInequalities.Probability.Stein.hessianMatrix W (gradient u x) * FunctionalInequalities.Probability.Stein.hessianMatrix u x) i j +
      (R x * (Matrix.of fun a b => T x i a b) * R x *
        (Matrix.of fun a b => T x j a b)).trace
    ∀ i j : Fin n,
      (∀ a : Fin n, ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
        MemLp (fun x => J x i j a) 2
          ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
      LocallyIntegrable (fun x => E x i j)
        (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
      LocallyIntegrable (fun x => Real.exp (-u x) * E x i j)
        (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
      ∀ ψ : EuclideanSpace ℝ (Fin n) → ℝ,
        ContDiff ℝ 1 ψ → HasCompactSupport ψ →
        (∫ x, Real.exp (-u x) * (∑ a : Fin n, J x i j a *
          fderiv ℝ ψ x (EuclideanSpace.basisFun (Fin n) ℝ a))
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
        -(∫ x, Real.exp (-u x) * E x i j * ψ x
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))) ∧
    let R := fun x => (FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹
    let J := fun x i j a => ∑ b : Fin n, R x b a * T x b i j
    let E := fun x i j => -FunctionalInequalities.Probability.Stein.hessianMatrix u x i j +
      (FunctionalInequalities.Probability.Stein.hessianMatrix u x * FunctionalInequalities.Probability.Stein.hessianMatrix W (gradient u x) * FunctionalInequalities.Probability.Stein.hessianMatrix u x) i j +
      (R x * (Matrix.of fun a b => T x i a b) * R x *
        (Matrix.of fun a b => T x j a b)).trace
    ∀ ψ : EuclideanSpace ℝ (Fin n) → ℝ,
      ContDiff ℝ 1 ψ → HasCompactSupport ψ → ∀ l k i j : Fin n,
      (∀ b : Fin n, Integrable (fun x => Real.exp (-u x) * J x i j b * (ψ x * T x b l k + fderiv ℝ ψ x (EuclideanSpace.basisFun (Fin n) ℝ b) * FunctionalInequalities.Probability.Stein.hessianMatrix u x l k))
        (volume : Measure (EuclideanSpace ℝ (Fin n)))) ∧
      Integrable (fun x => Real.exp (-u x) * E x i j * (ψ x * FunctionalInequalities.Probability.Stein.hessianMatrix u x l k))
        (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
      (∫ x, Real.exp (-u x) * (∑ b : Fin n, J x i j b * (ψ x * T x b l k + fderiv ℝ ψ x (EuclideanSpace.basisFun (Fin n) ℝ b) * FunctionalInequalities.Probability.Stein.hessianMatrix u x l k))
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
      -(∫ x, Real.exp (-u x) * E x i j * (ψ x * FunctionalInequalities.Probability.Stein.hessianMatrix u x l k)
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))) ∧
      ∃ c C : ℝ, 0 ≤ C ∧ (∀ x, 1 ≤ u x - c) ∧
      let χ := fun R x => Real.smoothTransition (2 - (u x - c) / R)
      let Lχ := fun R x => ((FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹ * FunctionalInequalities.Probability.Stein.hessianMatrix (χ R) x).trace -
        fderiv ℝ W (gradient u x) (gradient (χ R) x)
      (∀ R : ℝ, 1 ≤ R → ContDiff ℝ 1 (χ R) ∧ HasCompactSupport (χ R) ∧
        (∃ K : NNReal, LipschitzWith K (gradient (χ R))) ∧
        ∀ x, 0 ≤ χ R x ∧ χ R x ≤ 1) ∧
      (∀ x, MonotoneOn (fun R => χ R x) (Ici 1)) ∧
      (∀ x, Tendsto (fun R => χ R x) atTop (𝓝 1)) ∧
      (∀ R : ℝ, 1 ≤ R → Integrable (Lχ R)
        ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u))) ∧
      (∀ R : ℝ, 1 ≤ R → (∫ x, |Lχ R x|
        ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u))) ≤ C / R) ∧
      Tendsto (fun R : ℝ => ∫ x, |Lχ R x|
        ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u))) atTop (𝓝 0) ∧
      ∀ r : ℝ, 1 ≤ r → ∀ (η : EuclideanSpace ℝ (Fin n) → ℝ)
        (a : Fin n → EuclideanSpace ℝ (Fin n) → ℝ) (Cη : ℝ),
        LocallyIntegrable η (volume : Measure (EuclideanSpace ℝ (Fin n))) →
        (∀ x, ‖η x‖ ≤ Cη) →
        (∀ i : Fin n, FunctionalInequalities.Analysis.HasWeakDerivAlong η (a i) (EuclideanSpace.basisFun (Fin n) ℝ i)) →
        (∀ i : Fin n, ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
          MemLp (a i) 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) →
        Integrable (fun x => η x * Lχ r x * Real.exp (-u x))
          (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
        Integrable (fun x => (∑ i : Fin n, ∑ j : Fin n, (FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹ i j *
          a i x * fderiv ℝ (χ r) x (EuclideanSpace.basisFun (Fin n) ℝ j)) * Real.exp (-u x))
          (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
        (∫ x, η x * Lχ r x * Real.exp (-u x)
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
        -(∫ x, (∑ i : Fin n, ∑ j : Fin n, (FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹ i j *
          a i x * fderiv ℝ (χ r) x (EuclideanSpace.basisFun (Fin n) ℝ j)) * Real.exp (-u x)
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) := by
  obtain ⟨u, L, LF, T, hrest, c, C, hC, hlower, hreg, hmono, hpoint, hint, hbound, hdecay⟩ :=
    FunctionalInequalities.Analysis.exists_regular_moment_weak_cutoffs_408915f hn hκ hK hKc hKint hW hstrong μ hμ hiso
  have hcopy := hrest
  rcases hcopy with ⟨_hc, _hl, hnrm, _hm, hC1, hG, hF, _hw, hd, _hT, _he,
    _hfirst, hInv, _hmean, _hq, _hflux, _hweighted, _hbounded⟩
  have hdet : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      (FunctionalInequalities.Probability.Stein.hessianMatrix u x).det = Real.exp (-u x + W (gradient u x)) := by
    filter_upwards [hd] with x hx
    rw [← hx.2.1, Real.exp_log hx.1.det_pos]
  refine ⟨u, L, LF, T, hrest, c, C, hC, hlower, hreg, hmono, hpoint, hint, hbound, hdecay, ?_⟩
  dsimp only
  intro r hr η a Cη hη hηbound hweak ha2
  obtain ⟨Gr, hGr⟩ := (hreg r hr).2.2.1
  have hexp := FunctionalInequalities.Analysis.BakryEmery.integrable_exp_neg_of_integral_eq_one
    (volume : Measure (EuclideanSpace ℝ (Fin n))) u hnrm
  have hForce := (integrable_tilted_iff hexp _).mp (hint r hr)
  apply FunctionalInequalities.Analysis.integral_rough_mul_generator_eq_neg_energy_of_contDiff_one_408915f hC1 hG
    (hW.of_le (WithTop.coe_le_coe.mpr le_top)) hF hdet
    (hreg r hr).1 hGr (hreg r hr).2.1
    (fun i j S hS => (hInv i i j).2.2 S hS) _ hη hηbound hweak ha2
  simpa only [Pi.neg_apply, smul_eq_mul, mul_comm] using hForce
