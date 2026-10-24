-- Prove2me | solution 1 for FunctionalInequalities.Analysis.integral_array_pair_balance_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T15:38:41.206388+00:00
-- url     : https://prove2.me/submissions/52a57b4b-5fd4-4747-a155-3281354af2bc

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

noncomputable section
section ArrayPairBalance
open MeasureTheory
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
set_option maxHeartbeats 1200000 in
/-- Finite integral balance of paired integrable arrays; one-use support of the flux identity. -/
 theorem solution {n : ℕ}
    (A B C D : Fin n → Fin n → EuclideanSpace ℝ (Fin n) → ℝ)
    (F : EuclideanSpace ℝ (Fin n) → ℝ)
    (hA : ∀ a b, Integrable (A a b) (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hB : ∀ a b, Integrable (B a b) (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hC : ∀ a b, Integrable (C a b) (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hD : ∀ a b, Integrable (D a b) (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hF : Integrable F (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hPair : ∀ a b,
      (∫ x, A a b x + B a b x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
        ∫ x, C a b x + D a b x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hTrace : (∫ x, ∑ a : Fin n, ∑ b : Fin n, D a b x
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
      -(∫ x, F x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))) :
    (∫ x, ∑ a : Fin n, ∑ b : Fin n, B a b x
      ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
    -(∫ x, F x - (∑ a : Fin n, ∑ b : Fin n, C a b x) +
      ∑ a : Fin n, ∑ b : Fin n, A a b x
      ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) := by
  have hA_inner :
      ∀ a : Fin n,
        Integrable (fun x => ∑ b : Fin n, A a b x)
          (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    intro a
    apply integrable_finsetSum (μ := (volume : Measure (EuclideanSpace ℝ (Fin n))))
      Finset.univ
    intro b _
    exact hA a b
  have hB_inner :
      ∀ a : Fin n,
        Integrable (fun x => ∑ b : Fin n, B a b x)
          (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    intro a
    apply integrable_finsetSum (μ := (volume : Measure (EuclideanSpace ℝ (Fin n))))
      Finset.univ
    intro b _
    exact hB a b
  have hC_inner :
      ∀ a : Fin n,
        Integrable (fun x => ∑ b : Fin n, C a b x)
          (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    intro a
    apply integrable_finsetSum (μ := (volume : Measure (EuclideanSpace ℝ (Fin n))))
      Finset.univ
    intro b _
    exact hC a b
  have hD_inner :
      ∀ a : Fin n,
        Integrable (fun x => ∑ b : Fin n, D a b x)
          (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    intro a
    apply integrable_finsetSum (μ := (volume : Measure (EuclideanSpace ℝ (Fin n))))
      Finset.univ
    intro b _
    exact hD a b
  have hA_total :
      Integrable (fun x => ∑ a : Fin n, ∑ b : Fin n, A a b x)
        (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    apply integrable_finsetSum (μ := (volume : Measure (EuclideanSpace ℝ (Fin n))))
      Finset.univ
    intro a _
    exact hA_inner a
  have hC_total :
      Integrable (fun x => ∑ a : Fin n, ∑ b : Fin n, C a b x)
        (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    apply integrable_finsetSum (μ := (volume : Measure (EuclideanSpace ℝ (Fin n))))
      Finset.univ
    intro a _
    exact hC_inner a
  have hIA :
      (∫ x, ∑ a : Fin n, ∑ b : Fin n, A a b x
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
        ∑ a : Fin n, ∑ b : Fin n,
          ∫ x, A a b x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    calc
      (∫ x, ∑ a : Fin n, ∑ b : Fin n, A a b x
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
          ∑ a : Fin n, ∫ x, ∑ b : Fin n, A a b x
            ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := by
        exact integral_finsetSum
          (μ := (volume : Measure (EuclideanSpace ℝ (Fin n)))) Finset.univ
          (fun a _ => hA_inner a)
      _ = ∑ a : Fin n, ∑ b : Fin n,
          ∫ x, A a b x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := by
        apply Finset.sum_congr rfl
        intro a _
        exact integral_finsetSum
          (μ := (volume : Measure (EuclideanSpace ℝ (Fin n)))) Finset.univ
          (fun b _ => hA a b)
  have hIB :
      (∫ x, ∑ a : Fin n, ∑ b : Fin n, B a b x
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
        ∑ a : Fin n, ∑ b : Fin n,
          ∫ x, B a b x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    calc
      (∫ x, ∑ a : Fin n, ∑ b : Fin n, B a b x
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
          ∑ a : Fin n, ∫ x, ∑ b : Fin n, B a b x
            ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := by
        exact integral_finsetSum
          (μ := (volume : Measure (EuclideanSpace ℝ (Fin n)))) Finset.univ
          (fun a _ => hB_inner a)
      _ = ∑ a : Fin n, ∑ b : Fin n,
          ∫ x, B a b x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := by
        apply Finset.sum_congr rfl
        intro a _
        exact integral_finsetSum
          (μ := (volume : Measure (EuclideanSpace ℝ (Fin n)))) Finset.univ
          (fun b _ => hB a b)
  have hIC :
      (∫ x, ∑ a : Fin n, ∑ b : Fin n, C a b x
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
        ∑ a : Fin n, ∑ b : Fin n,
          ∫ x, C a b x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    calc
      (∫ x, ∑ a : Fin n, ∑ b : Fin n, C a b x
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
          ∑ a : Fin n, ∫ x, ∑ b : Fin n, C a b x
            ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := by
        exact integral_finsetSum
          (μ := (volume : Measure (EuclideanSpace ℝ (Fin n)))) Finset.univ
          (fun a _ => hC_inner a)
      _ = ∑ a : Fin n, ∑ b : Fin n,
          ∫ x, C a b x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := by
        apply Finset.sum_congr rfl
        intro a _
        exact integral_finsetSum
          (μ := (volume : Measure (EuclideanSpace ℝ (Fin n)))) Finset.univ
          (fun b _ => hC a b)
  have hID :
      (∫ x, ∑ a : Fin n, ∑ b : Fin n, D a b x
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
        ∑ a : Fin n, ∑ b : Fin n,
          ∫ x, D a b x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    calc
      (∫ x, ∑ a : Fin n, ∑ b : Fin n, D a b x
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
          ∑ a : Fin n, ∫ x, ∑ b : Fin n, D a b x
            ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := by
        exact integral_finsetSum
          (μ := (volume : Measure (EuclideanSpace ℝ (Fin n)))) Finset.univ
          (fun a _ => hD_inner a)
      _ = ∑ a : Fin n, ∑ b : Fin n,
          ∫ x, D a b x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := by
        apply Finset.sum_congr rfl
        intro a _
        exact integral_finsetSum
          (μ := (volume : Measure (EuclideanSpace ℝ (Fin n)))) Finset.univ
          (fun b _ => hD a b)
  have hPairSum :
      (∑ a : Fin n, ∑ b : Fin n,
        ((∫ x, A a b x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) +
          (∫ x, B a b x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))))) =
      (∑ a : Fin n, ∑ b : Fin n,
        ((∫ x, C a b x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) +
          (∫ x, D a b x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))))) := by
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    have h := hPair a b
    rw [integral_add (hA a b) (hB a b),
      integral_add (hC a b) (hD a b)] at h
    exact h
  have hSums :
      (∑ a : Fin n, ∑ b : Fin n,
        (∫ x, A a b x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))) +
        (∑ a : Fin n, ∑ b : Fin n,
          (∫ x, B a b x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))) =
      (∑ a : Fin n, ∑ b : Fin n,
        (∫ x, C a b x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))) +
        (∑ a : Fin n, ∑ b : Fin n,
          (∫ x, D a b x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))) := by
    simpa only [Finset.sum_add_distrib] using hPairSum
  have hBalance :
      (∫ x, ∑ a : Fin n, ∑ b : Fin n, A a b x
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) +
        (∫ x, ∑ a : Fin n, ∑ b : Fin n, B a b x
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
      (∫ x, ∑ a : Fin n, ∑ b : Fin n, C a b x
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) +
        (∫ x, ∑ a : Fin n, ∑ b : Fin n, D a b x
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) := by
    calc
      (∫ x, ∑ a : Fin n, ∑ b : Fin n, A a b x
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) +
          (∫ x, ∑ a : Fin n, ∑ b : Fin n, B a b x
            ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
          (∑ a : Fin n, ∑ b : Fin n,
            ∫ x, A a b x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) +
          (∑ a : Fin n, ∑ b : Fin n,
            ∫ x, B a b x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) := by
        rw [hIA, hIB]
      _ =
          (∑ a : Fin n, ∑ b : Fin n,
            ∫ x, C a b x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) +
          (∑ a : Fin n, ∑ b : Fin n,
            ∫ x, D a b x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) := hSums
      _ =
          (∫ x, ∑ a : Fin n, ∑ b : Fin n, C a b x
            ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) +
          (∫ x, ∑ a : Fin n, ∑ b : Fin n, D a b x
            ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) := by
        rw [← hIC, ← hID]
  have hDTrace :
      (∑ a : Fin n, ∑ b : Fin n,
          ∫ x, D a b x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
        -(∫ x, F x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) := by
    calc
      (∑ a : Fin n, ∑ b : Fin n,
          ∫ x, D a b x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
          ∫ x, ∑ a : Fin n, ∑ b : Fin n, D a b x
            ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := hID.symm
      _ = -(∫ x, F x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) := hTrace
  have hExpand :
      (∫ x, F x - (∑ a : Fin n, ∑ b : Fin n, C a b x) +
          ∑ a : Fin n, ∑ b : Fin n, A a b x
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
        (∫ x, F x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) -
          (∫ x, ∑ a : Fin n, ∑ b : Fin n, C a b x
            ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) +
          (∫ x, ∑ a : Fin n, ∑ b : Fin n, A a b x
            ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) := by
    calc
      (∫ x, F x - (∑ a : Fin n, ∑ b : Fin n, C a b x) +
          ∑ a : Fin n, ∑ b : Fin n, A a b x
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
          (∫ x, F x - (∑ a : Fin n, ∑ b : Fin n, C a b x)
            ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) +
            (∫ x, ∑ a : Fin n, ∑ b : Fin n, A a b x
              ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) := by
        exact integral_add (hF.sub hC_total) hA_total
      _ =
          (∫ x, F x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) -
            (∫ x, ∑ a : Fin n, ∑ b : Fin n, C a b x
              ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) +
            (∫ x, ∑ a : Fin n, ∑ b : Fin n, A a b x
              ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) := by
        rw [integral_sub hF hC_total]
  rw [hExpand]
  linarith [hBalance, hDTrace]
