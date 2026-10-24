-- Prove2me | solution 1 for FunctionalInequalities.Analysis.integral_profile_inverse_energy_eq_drift_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T15:42:39.570787+00:00
-- url     : https://prove2.me/submissions/e5629535-e987-40e0-86b3-cefcc4bb069d

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
import Theorems.Thm_FunctionalInequalities_Analysis_integrable_inv_hessianMatrix_mul_of_bounded_compact_408915f
import Theorems.Thm_FunctionalInequalities_Analysis_integral_mul_generator_eq_neg_energy_of_contDiff_one_408915f

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
private theorem FunctionalInequalities.Analysis.integrable_compact_C1_inverse_energy {n : ℕ}
    {u V η w : EuclideanSpace ℝ (Fin n) → ℝ} {G LF : NNReal}
    (hu : ContDiff ℝ 1 u) (hG : LipschitzWith G (gradient u))
    (hF : LipschitzWith LF (fun x => -u x + V (gradient u x)))
    (hdet : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      (hessianMatrix u x).det = Real.exp (-u x + V (gradient u x)))
    (hη : ContDiff ℝ 1 η) (hηc : HasCompactSupport η) (hw : ContDiff ℝ 1 w) :
    Integrable (fun x =>
      (∑ i : Fin n, ∑ j : Fin n, (hessianMatrix u x)⁻¹ i j *
        fderiv ℝ η x (EuclideanSpace.basisFun (Fin n) ℝ i) *
        fderiv ℝ w x (EuclideanSpace.basisFun (Fin n) ℝ j)) * Real.exp (-u x))
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
  classical
  let e := EuclideanSpace.basisFun (Fin n) ℝ
  have hi (i j : Fin n) : Integrable
      (fun x => (hessianMatrix u x)⁻¹ i j *
        (fderiv ℝ η x (e i) * fderiv ℝ w x (e j) * Real.exp (-u x)))
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    have hc : Continuous
        (fun x => fderiv ℝ η x (e i) * fderiv ℝ w x (e j) * Real.exp (-u x)) :=
      (((hη.continuous_fderiv one_ne_zero).clm_apply continuous_const).mul
        ((hw.continuous_fderiv one_ne_zero).clm_apply continuous_const)).mul
        (Real.continuous_exp.comp hu.continuous.neg)
    have hs : HasCompactSupport
        (fun x => fderiv ℝ η x (e i) * fderiv ℝ w x (e j) * Real.exp (-u x)) :=
      (hηc.fderiv_apply ℝ (e i)).mul_right.mul_right
    obtain ⟨C, hC⟩ := hs.exists_bound_of_continuous hc
    exact integrable_inv_hessianMatrix_mul_of_bounded_compact_408915f
      hG hF.continuous hdet hc.measurable hs hC i j
  have hs := integrable_finsetSum Finset.univ
    (fun i _ => integrable_finsetSum Finset.univ (fun j _ => hi i j))
  simpa only [Finset.sum_mul, mul_assoc] using hs
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities.Analysis in
 theorem solution {n : ℕ}
    {u V : EuclideanSpace ℝ (Fin n) → ℝ} {ζ : ℝ → ℝ} {G LF : NNReal}
    (hu : ContDiff ℝ 1 u) (hG : LipschitzWith G (gradient u))
    (hV : ContDiff ℝ 1 V)
    (hF : LipschitzWith LF (fun x => -u x + V (gradient u x)))
    (hdet : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      (FunctionalInequalities.Probability.Stein.hessianMatrix u x).det = Real.exp (-u x + V (gradient u x)))
    (hζ : ContDiff ℝ 1 ζ) (hζc : HasCompactSupport (fun x => ζ (u x))) :
    Integrable (fun x =>
      (deriv ζ (u x) * (∑ i : Fin n, ∑ j : Fin n, (FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹ i j *
        fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ i) *
        fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ j))) * Real.exp (-u x))
      (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
    (∫ x, -(deriv ζ (u x) * (∑ i : Fin n, ∑ j : Fin n, (FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹ i j *
        fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ i) *
        fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ j))) * Real.exp (-u x)
      ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
    ∫ x, ζ (u x) * ((n : ℝ) - fderiv ℝ V (gradient u x) (gradient u x)) *
      Real.exp (-u x) ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := by
  let e := EuclideanSpace.basisFun (Fin n) ℝ
  have hη : ContDiff ℝ 1 (fun x => ζ (u x)) := hζ.comp hu
  have hchain (x : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
      fderiv ℝ (fun y => ζ (u y)) x (e i) =
        deriv ζ (u x) * fderiv ℝ u x (e i) := by
    have hd := ((hζ.differentiable one_ne_zero (u x)).hasDerivAt.comp_hasFDerivAt
      x (hu.differentiable one_ne_zero x).hasFDerivAt).fderiv
    change fderiv ℝ (fun y => ζ (u y)) x = _ at hd
    rw [hd]
    rfl
  have heq (x : EuclideanSpace ℝ (Fin n)) :
      (∑ i : Fin n, ∑ j : Fin n, (FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹ i j *
        fderiv ℝ (fun y => ζ (u y)) x (e i) * fderiv ℝ u x (e j)) =
      deriv ζ (u x) * (∑ i : Fin n, ∑ j : Fin n, (FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹ i j *
        fderiv ℝ u x (e i) * fderiv ℝ u x (e j)) := by
    simp only [hchain, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hi := integrable_compact_C1_inverse_energy hu hG hF hdet hη hζc hu
  have hp := FunctionalInequalities.Analysis.integral_mul_generator_eq_neg_energy_of_contDiff_one_408915f
    hu hG hV hF hdet hu hG hη hζc
  have htr : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      ((FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹ * FunctionalInequalities.Probability.Stein.hessianMatrix u x).trace = (n : ℝ) := by
    filter_upwards [hdet] with x hx
    rw [Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr
      (hx.trans_ne (Real.exp_ne_zero _)))]
    simp only [Matrix.trace_one, Fintype.card_fin]
  have hiq := hi.congr (Filter.Eventually.of_forall fun x =>
    congrArg (fun t : ℝ => t * Real.exp (-u x)) (heq x))
  have hEq :
      (∫ x, (∑ i : Fin n, ∑ j : Fin n, (FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹ i j *
        fderiv ℝ (fun y => ζ (u y)) x (e i) * fderiv ℝ u x (e j)) * Real.exp (-u x)
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
      ∫ x, (deriv ζ (u x) * (∑ i : Fin n, ∑ j : Fin n, (FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹ i j *
        fderiv ℝ u x (e i) * fderiv ℝ u x (e j))) * Real.exp (-u x)
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    integral_congr_ae (Filter.Eventually.of_forall fun x =>
      congrArg (fun t : ℝ => t * Real.exp (-u x)) (heq x))
  refine ⟨hiq, ?_⟩
  calc
    _ = -(∫ x, (deriv ζ (u x) * (∑ i : Fin n, ∑ j : Fin n, (FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹ i j *
        fderiv ℝ u x (e i) * fderiv ℝ u x (e j))) * Real.exp (-u x)
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) := by
      simpa only [neg_mul] using integral_neg
        (fun x => (deriv ζ (u x) * (∑ i : Fin n, ∑ j : Fin n, (FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹ i j *
          fderiv ℝ u x (e i) * fderiv ℝ u x (e j))) * Real.exp (-u x))
    _ = _ := (congrArg Neg.neg hEq).symm
    _ = _ := hp.symm
    _ = _ := integral_congr_ae (htr.mono fun x hx =>
      congrArg (fun t : ℝ => ζ (u x) *
        (t - fderiv ℝ V (gradient u x) (gradient u x)) * Real.exp (-u x)) hx)
