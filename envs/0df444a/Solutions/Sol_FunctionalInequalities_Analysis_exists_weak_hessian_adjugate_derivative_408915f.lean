-- Prove2me | solution 1 for FunctionalInequalities.Analysis.exists_weak_hessian_adjugate_derivative_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T15:39:33.705622+00:00
-- url     : https://prove2.me/submissions/229eca1b-d9ef-4d08-98af-2fc49e786484

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_HessianOperator
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
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.SpecificCodomains.Pi
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Algebra.Group.Matrix
import Mathlib.Topology.MetricSpace.Lipschitz
import Theorems.Thm_FunctionalInequalities_Analysis_hasWeakDerivAlong_det_of_locally_memLp_two_408915f
import Theorems.Thm_FunctionalInequalities_Analysis_hasWeakDerivAlong_of_contDiff_408915f

noncomputable section
open Matrix
open FunctionalInequalities.Probability.Stein
section WeakHessianAdjugateConsumers
open MeasureTheory Set Filter Metric Matrix
open scoped ContDiff Topology Matrix.Norms.Elementwise
open FunctionalInequalities.Probability.Stein
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
/-- Existing cofactor proof core, for the same supplied actual tensor. -/
theorem solution {n : ℕ}
    {u : EuclideanSpace ℝ (Fin n) → ℝ}
    {T : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → Fin n → ℝ}
    (hbound : ∀ r s : Fin n, MemLp (fun x => FunctionalInequalities.Probability.Stein.hessianMatrix u x r s)
      (⊤ : ENNReal) (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hT : ∀ k i j : Fin n,
      FunctionalInequalities.Analysis.HasWeakDerivAlong (fun x => FunctionalInequalities.Probability.Stein.hessianMatrix u x i j) (fun x => T x k i j)
        (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
      ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
        MemLp (fun x => T x k i j) 2
          ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S))
    (k i j : Fin n) :
    ∃ g : EuclideanSpace ℝ (Fin n) → ℝ,
      FunctionalInequalities.Analysis.HasWeakDerivAlong (fun x => (FunctionalInequalities.Probability.Stein.hessianMatrix u x).adjugate i j) g
        (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
      ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
        MemLp g 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) := by
  classical
  let A : EuclideanSpace ℝ (Fin n) → Matrix (Fin n) (Fin n) ℝ :=
    fun x => (FunctionalInequalities.Probability.Stein.hessianMatrix u x).updateRow j (Pi.single i 1)
  let DA : EuclideanSpace ℝ (Fin n) → Matrix (Fin n) (Fin n) ℝ :=
    fun x => (Matrix.of fun r s => T x k r s).updateRow j (fun _ => 0)
  have hA (r s : Fin n) : FunctionalInequalities.Analysis.HasWeakDerivAlong (fun x => A x r s)
      (fun x => DA x r s) (EuclideanSpace.basisFun (Fin n) ℝ k) := by
    by_cases hr : r = j
    · subst r
      simpa [A, DA, Matrix.updateRow_apply] using
        (FunctionalInequalities.Analysis.hasWeakDerivAlong_of_contDiff_408915f
          (f := fun _ : EuclideanSpace ℝ (Fin n) => (Pi.single i (1 : ℝ) : Fin n → ℝ) s)
          contDiff_const (EuclideanSpace.basisFun (Fin n) ℝ k))
    · simpa [A, DA, Matrix.updateRow_apply, hr] using (hT k r s).1
  have hAb (r s : Fin n) : MemLp (fun x => A x r s) (⊤ : ENNReal)
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    by_cases hr : r = j
    · subst r
      simpa [A, Matrix.updateRow_apply] using
        (memLp_top_const ((Pi.single i (1 : ℝ) : Fin n → ℝ) s)
          (μ := (volume : Measure (EuclideanSpace ℝ (Fin n)))))
    · simpa [A, Matrix.updateRow_apply, hr] using hbound r s
  have hDA2 (r s : Fin n) (S : Set (EuclideanSpace ℝ (Fin n))) (hS : IsCompact S) :
      MemLp (fun x => DA x r s) 2
        ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) := by
    by_cases hr : r = j
    · subst r
      simp [DA, Matrix.updateRow_apply]
    · simpa [DA, Matrix.updateRow_apply, hr] using (hT k r s).2 S hS
  have hp := FunctionalInequalities.Analysis.hasWeakDerivAlong_det_of_locally_memLp_two_408915f hA hAb hDA2
  refine ⟨_, ?_, hp.2⟩
  simpa only [Matrix.adjugate_apply] using hp.1
