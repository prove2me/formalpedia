-- Prove2me | solution 1 for FunctionalInequalities.Analysis.localLp_hessian_flux_trace_forcing_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T15:37:40.127774+00:00
-- url     : https://prove2.me/submissions/ae995ecb-ab23-4b23-b30a-07b18af88306

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Bochner_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Gamma
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_HessianOperator
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_InverseHessian_Weak
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Laplacian
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_MongeAmpere
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_WeakHessian
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Cutoff_LipschitzBall
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Cutoff_SmoothBall
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Lipschitz_Gradient
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Matrix_DeterminantDerivative
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Matrix_Piola
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Matrix_Positivity
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Operator_Coordinates
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_WeakDerivative_Basic
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
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Norm
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Calculus.TaylorIntegral
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Star
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.SpecificCodomains.Pi
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Algebra.Group.Matrix
import Mathlib.Topology.Algebra.MetricSpace.Lipschitz
import Mathlib.Topology.Algebra.Support
import Mathlib.Topology.EMetricSpace.Lipschitz
import Mathlib.Topology.MetricSpace.Lipschitz

section
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
/-- The product of two functions that are L2 on every compact set is locally integrable. -/
theorem FunctionalInequalities.Analysis.locallyIntegrable_mul_of_compact_L2 {n : ℕ}
    {f g : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
      MemLp f 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S))
    (hg : ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
      MemLp g 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) :
    LocallyIntegrable (fun x => f x * g x)
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
  apply locallyIntegrable_iff.mpr
  intro S hS
  exact (hf S hS).integrable_mul (hg S hS)
end
end
end SharedCompactLocalTools
end
end

noncomputable section
section HessianFluxTraceForcing
open MeasureTheory Set Filter
open FunctionalInequalities.Probability.Stein
open scoped ContDiff RealInnerProductSpace Topology
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
set_option maxHeartbeats 800000 in
/-- Compact-local L2 Hessian flux `Jᵢⱼₐ = Σ_b (H⁻¹)_{ba} T_{bij}` and local integrability of the trace
forcing `Cᵢⱼ` from compact-local L2 tensor and inverse-derivative data and compact-local inverse bounds. -/
theorem solution {n : ℕ}
    {u : EuclideanSpace ℝ (Fin n) → ℝ}
    (T : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → Fin n → ℝ)
    (hT2 : ∀ k i j : Fin n, ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
      MemLp (fun x => T x k i j) 2
        ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S))
    (hInv2 : ∀ k i j : Fin n, ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
      MemLp (fun x => -(((FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹ *
        (Matrix.of fun a b => T x k a b) * (FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹) i j)) 2
        ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S))
    (hRtop : ∀ i j : Fin n, ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
      MemLp (fun x => (FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹ i j) (⊤ : ENNReal)
        ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S))
    (Q : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → ℝ)
    (hQ : ∀ i j : Fin n, LocallyIntegrable (fun x => Q x i j)
      (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
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
        (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
  dsimp only
  intro i j
  constructor
  · intro a S hS
    apply MeasureTheory.memLp_finsetSum (Finset.univ : Finset (Fin n))
    intro b _hb
    exact (hT2 b i j S hS).mul' (hRtop b a S hS)
  · have hTD :
        LocallyIntegrable
          (fun x => ∑ a : Fin n, ∑ b : Fin n,
            T x i a b *
              -(((FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹ *
                (Matrix.of fun c d => T x j c d) *
                (FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹) b a))
          (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
      apply MeasureTheory.locallyIntegrable_finsetSum
        (Finset.univ : Finset (Fin n))
      intro a _ha
      apply MeasureTheory.locallyIntegrable_finsetSum
        (Finset.univ : Finset (Fin n))
      intro b _hb
      exact FunctionalInequalities.Analysis.locallyIntegrable_mul_of_compact_L2
        (hT2 i a b) (hInv2 j b a)
    have hdouble :
        LocallyIntegrable
          (fun x => ∑ b : Fin n, ∑ a : Fin n,
            T x b i j *
              -(((FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹ *
                (Matrix.of fun c d => T x a c d) *
                (FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹) b a))
          (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
      apply MeasureTheory.locallyIntegrable_finsetSum
        (Finset.univ : Finset (Fin n))
      intro b _hb
      apply MeasureTheory.locallyIntegrable_finsetSum
        (Finset.univ : Finset (Fin n))
      intro a _ha
      exact FunctionalInequalities.Analysis.locallyIntegrable_mul_of_compact_L2
        (hT2 b i j) (hInv2 a b a)
    have hRow :
        LocallyIntegrable
          (fun x => ∑ b : Fin n, T x b i j *
            (∑ a : Fin n,
              -(((FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹ *
                (Matrix.of fun c d => T x a c d) *
                (FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹) b a)))
          (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
      simpa only [Finset.mul_sum] using hdouble
    exact ((hQ i j).sub hTD).add hRow
