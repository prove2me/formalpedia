-- Prove2me | solution 1 for FunctionalInequalities.Analysis.integrable_inv_hessianMatrix_mul_of_bounded_compact_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T15:17:29.858458+00:00
-- url     : https://prove2.me/submissions/1c57c8fa-7d1e-4001-83c9-5459a1e849c2

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

noncomputable section
open Matrix
open FunctionalInequalities.Probability.Stein
section LN10AInverseHessianDivergence
open MeasureTheory Set Filter
open scoped Topology
open FunctionalInequalities.Probability.Stein
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
section StructuredSpace
variable {E : Type*}
variable [NormedAddCommGroup E]
private lemma FunctionalInequalities.Analysis.n10_hessian {n : ℕ}
    (u : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    hessianMatrix u x = FunctionalInequalities.Analysis.n10_matrix (fderiv ℝ (gradient u) x) := by
  let T : EuclideanSpace ℝ (Fin n) ≃L[ℝ]
      StrongDual ℝ (EuclideanSpace ℝ (Fin n)) :=
    (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).toContinuousLinearEquiv
  have he : fderiv ℝ u = T ∘ gradient u :=
    funext fun y => (T.apply_symm_apply (fderiv ℝ u y)).symm
  have hd :
      fderiv ℝ (fderiv ℝ u) x =
        T.toContinuousLinearMap.comp (fderiv ℝ (gradient u) x) :=
    (congrArg (fun f => fderiv ℝ f x) he).trans T.comp_fderiv
  ext r s
  change
    fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.basisFun (Fin n) ℝ r)
        (EuclideanSpace.basisFun (Fin n) ℝ s) =
      T (fderiv ℝ (gradient u) x (EuclideanSpace.basisFun (Fin n) ℝ r))
        (EuclideanSpace.basisFun (Fin n) ℝ s)
  rw [hd]
  rfl
private lemma FunctionalInequalities.Analysis.n10_continuous_cofactor {n : ℕ} (i j : Fin n) :
    Continuous
      (fun L : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) =>
        (FunctionalInequalities.Analysis.n10_matrix L).adjugate i j) := by
  let T : EuclideanSpace ℝ (Fin n) ≃L[ℝ]
      StrongDual ℝ (EuclideanSpace ℝ (Fin n)) :=
    (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).toContinuousLinearEquiv
  apply (continuous_apply j).comp
  apply (continuous_apply i).comp
  apply Continuous.matrix_adjugate
  apply continuous_pi
  intro r
  apply continuous_pi
  intro s
  exact
    (T.continuous.comp (continuous_id.clm_apply continuous_const)).clm_apply
      continuous_const
private lemma FunctionalInequalities.Analysis.n10_measurable_cofactor {n : ℕ}
    (u : EuclideanSpace ℝ (Fin n) → ℝ) (i j : Fin n) :
    Measurable (fun x => (hessianMatrix u x).adjugate i j) := by
  simpa only [n10_hessian, Function.comp_def] using
    (n10_continuous_cofactor i j).measurable.comp
      (measurable_fderiv ℝ (gradient u))
private lemma FunctionalInequalities.Analysis.n10_cofactor_bound {n : ℕ}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} {G : NNReal}
    (hG : LipschitzWith G (gradient u)) (i j : Fin n) :
    ∃ C : ℝ, ∀ x, ‖(hessianMatrix u x).adjugate i j‖ ≤ C := by
  obtain ⟨C, hC⟩ :=
    (isCompact_closedBall
      (0 : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
      (G : ℝ)).exists_bound_of_continuousOn
        (n10_continuous_cofactor i j).continuousOn
  refine ⟨C, fun x => ?_⟩
  rw [n10_hessian]
  apply hC
  change dist (fderiv ℝ (gradient u) x) 0 ≤ (G : ℝ)
  rw [dist_zero_right]
  exact norm_fderiv_le_of_lipschitz ℝ hG
end StructuredSpace
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities.Analysis in
/-- Compactly supported bounded multipliers are integrable against inverse-Hessian
entries under the existing weak Monge-Ampere assumptions for Letwin (2.2). -/
theorem solution {n : ℕ}
    {u F f : EuclideanSpace ℝ (Fin n) → ℝ}
    {G : NNReal} (hG : LipschitzWith G (gradient u)) (hF : Continuous F)
    (hdet : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      (FunctionalInequalities.Probability.Stein.hessianMatrix u x).det = Real.exp (F x))
    (hf : Measurable f) (hfc : HasCompactSupport f)
    {C : ℝ} (hC : ∀ x, ‖f x‖ ≤ C) (i j : Fin n) :
    Integrable (fun x => (FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹ i j * f x)
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
  classical
  have hw : Continuous (fun x => Real.exp (-F x)) :=
    Real.continuous_exp.comp hF.neg
  -- The bounded-compact argument of `n10_integrable_bounded_compact`,
  -- with continuous multiplication as in `n10_integrable_weighted_deriv`.
  have hl : LocallyIntegrable f
      (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    (memLp_top_of_bound hf.aestronglyMeasurable C
      (Filter.Eventually.of_forall hC)).locallyIntegrable le_top
  have hwl := LocallyIntegrable.continuous_mul hw hl
  have hwi : Integrable (fun x => Real.exp (-F x) * f x)
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    apply (hwl.integrableOn_isCompact hfc.isCompact).integrable_of_forall_notMem_eq_zero
    intro x hx
    rw [image_eq_zero_of_notMem_tsupport hx, mul_zero]
  obtain ⟨B, hB⟩ := n10_cofactor_bound hG i j
  have hi := hwi.bdd_mul
    (n10_measurable_cofactor u i j).aestronglyMeasurable
    (Filter.Eventually.of_forall hB)
  -- The AE inverse representation and congruence argument of
  -- `sum_integral_inv_hessianMatrix_mul_fderiv_eq` above.
  have hinv :
      ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
        (FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹ i j =
          Real.exp (-F x) * (FunctionalInequalities.Probability.Stein.hessianMatrix u x).adjugate i j := by
    filter_upwards [hdet] with x hx
    simp only [Matrix.inv_def, hx, Ring.inverse_eq_inv, Matrix.smul_apply,
      smul_eq_mul, Real.exp_neg]
  apply hi.congr
  filter_upwards [hinv] with x hx
  change (FunctionalInequalities.Probability.Stein.hessianMatrix u x).adjugate i j * (Real.exp (-F x) * f x) =
    (FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹ i j * f x
  rw [hx]
  ring
