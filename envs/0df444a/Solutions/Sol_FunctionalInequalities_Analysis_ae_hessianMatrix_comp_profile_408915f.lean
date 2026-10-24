-- Prove2me | solution 1 for FunctionalInequalities.Analysis.ae_hessianMatrix_comp_profile_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T15:40:41.399701+00:00
-- url     : https://prove2.me/submissions/14447d94-bdcc-4ef4-91ee-cd2200bc9709

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_HessianOperator
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_Basic
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
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
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
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.MeasureTheory.SpecificCodomains.Pi
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Algebra.Group.Matrix
import Mathlib.Topology.Algebra.MetricSpace.Lipschitz
import Mathlib.Topology.Algebra.Support
import Mathlib.Topology.EMetricSpace.Lipschitz
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.Order.Compact

section
noncomputable section
open InnerProductSpace
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
universe u
section DifferentialTools
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
section Gradient
variable [CompleteSpace E]
/-- Chain rule for the gradient: `∇(Φ ∘ g) = Φ'(g) ∇g`. -/
theorem FunctionalInequalities.Analysis.BakryEmery.gradient_comp {Φ : ℝ → ℝ} {g : E → ℝ} {x : E} (hΦ : DifferentiableAt ℝ Φ (g x))
    (hg : DifferentiableAt ℝ g x) :
    gradient (fun y => Φ (g y)) x = deriv Φ (g x) • gradient g x := by
  have hcomp : HasFDerivAt (fun y => Φ (g y)) (deriv Φ (g x) • fderiv ℝ g x) x :=
    hΦ.hasDerivAt.comp_hasFDerivAt x hg.hasFDerivAt
  unfold gradient
  rw [hcomp.fderiv, map_smul]
end Gradient
end DifferentialTools
end
end
end
end
end

noncomputable section
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
private lemma FunctionalInequalities.Analysis.differentiableAt_fderiv_of_differentiableAt_gradient
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {u : E → ℝ} {x : E} (hx : DifferentiableAt ℝ (gradient u) x) :
    DifferentiableAt ℝ (fderiv ℝ u) x := by
  have heq :
      fderiv ℝ u = (InnerProductSpace.toDual ℝ E) ∘ gradient u := by
    funext y
    simp [gradient]
  rw [heq]
  exact
    (InnerProductSpace.toDual ℝ E).toContinuousLinearEquiv.differentiableAt.comp x hx
private lemma FunctionalInequalities.Analysis.hessian_coord_of_gradient_diff
    {n : ℕ} {u : EuclideanSpace ℝ (Fin n) → ℝ} {x : EuclideanSpace ℝ (Fin n)}
    {i j : Fin n} (hx : DifferentiableAt ℝ (gradient u) x) :
    fderiv ℝ (fun y => fderiv ℝ u y (EuclideanSpace.basisFun (Fin n) ℝ j)) x
        (EuclideanSpace.basisFun (Fin n) ℝ i) =
      hessianMatrix u x i j := by
  have hfd : DifferentiableAt ℝ (fderiv ℝ u) x :=
    differentiableAt_fderiv_of_differentiableAt_gradient hx
  have hc :
      DifferentiableAt ℝ
        (fun _ : EuclideanSpace ℝ (Fin n) =>
          EuclideanSpace.basisFun (Fin n) ℝ j) x :=
    (differentiable_const (EuclideanSpace.basisFun (Fin n) ℝ j) :
      Differentiable ℝ
        (fun _ : EuclideanSpace ℝ (Fin n) =>
          EuclideanSpace.basisFun (Fin n) ℝ j)).differentiableAt
  have h := fderiv_clm_apply hfd hc
  have h' := congrArg
    (fun L : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ =>
      L (EuclideanSpace.basisFun (Fin n) ℝ i)) h
  simpa [hessianMatrix, bilinearIteratedFDerivTwo] using h'
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities.Analysis in
 theorem solution {n : ℕ}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} {ζ : ℝ → ℝ} {G : NNReal}
    (hu : ContDiff ℝ 1 u) (hG : LipschitzWith G (gradient u))
    (hζ : ContDiff ℝ 2 ζ) :
    ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))), ∀ i j : Fin n,
      FunctionalInequalities.Probability.Stein.hessianMatrix (fun y => ζ (u y)) x i j =
        deriv ζ (u x) * FunctionalInequalities.Probability.Stein.hessianMatrix u x i j +
          deriv (deriv ζ) (u x) *
            fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ i) *
            fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ j) := by
  let e := EuclideanSpace.basisFun (Fin n) ℝ
  let χ := fun y => ζ (u y)
  let coeff := fun y => deriv ζ (u y)
  have hζd : ContDiff ℝ 1 (deriv ζ) := hζ.deriv'
  have hcoeff : ContDiff ℝ 1 coeff := hζd.comp hu
  have hgrad : gradient χ = fun y => coeff y • gradient u y := by
    funext y
    exact FunctionalInequalities.Analysis.BakryEmery.gradient_comp
      ((hζ.differentiable (by norm_num)).differentiableAt)
      ((hu.differentiable one_ne_zero).differentiableAt)
  have hcoord (j : Fin n) :
      (fun y => fderiv ℝ χ y (e j)) =
        (fun y => coeff y * fderiv ℝ u y (e j)) := by
    funext y
    have hd := ((hζ.differentiable (by norm_num) (u y)).hasDerivAt.comp_hasFDerivAt
      y (hu.differentiable one_ne_zero y).hasFDerivAt).fderiv
    change fderiv ℝ χ y (e j) = _
    change fderiv ℝ χ y = _ at hd
    rw [hd]
    rfl
  filter_upwards [hG.ae_differentiableAt (μ := volume)] with x hx
  have hχx : DifferentiableAt ℝ (gradient χ) x := by
    rw [hgrad]
    exact ((hcoeff.differentiable one_ne_zero).differentiableAt).smul hx
  have hux := (hu.differentiable one_ne_zero x).hasFDerivAt
  have hcderiv : HasFDerivAt coeff
      (deriv (deriv ζ) (u x) • fderiv ℝ u x) x :=
    (hζd.differentiable one_ne_zero (u x)).hasDerivAt.comp_hasFDerivAt x hux
  intro i j
  have hduj : DifferentiableAt ℝ (fun y => fderiv ℝ u y (e j)) x := by
    simpa [Function.comp_def, inner_gradient_left] using
      (((innerSL ℝ) (e j)).differentiableAt.comp x hx)
  have hprod := (hcderiv.mul hduj.hasFDerivAt).fderiv
  change fderiv ℝ (fun y => coeff y * fderiv ℝ u y (e j)) x = _ at hprod
  calc
    FunctionalInequalities.Probability.Stein.hessianMatrix χ x i j = fderiv ℝ (fun y => fderiv ℝ χ y (e j)) x (e i) :=
      (hessian_coord_of_gradient_diff hχx).symm
    _ = fderiv ℝ (fun y => coeff y * fderiv ℝ u y (e j)) x (e i) := by rw [hcoord j]
    _ = _ := by
      rw [hprod]
      simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul]
      rw [hessian_coord_of_gradient_diff hx]
      dsimp only [coeff]
      ring
