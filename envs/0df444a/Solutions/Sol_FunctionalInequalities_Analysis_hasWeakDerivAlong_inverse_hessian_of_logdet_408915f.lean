-- Prove2me | solution 1 for FunctionalInequalities.Analysis.hasWeakDerivAlong_inverse_hessian_of_logdet_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T15:41:26.931512+00:00
-- url     : https://prove2.me/submissions/76d31df0-1426-44c0-8869-5ee3862f7309

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_HessianOperator
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_InverseHessian_Weak
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
import Mathlib.Data.Real.Star
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Matrix.Hermitian
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
import Mathlib.Topology.Algebra.MetricSpace.Lipschitz
import Mathlib.Topology.Algebra.Support
import Mathlib.Topology.EMetricSpace.Lipschitz
import Mathlib.Topology.MetricSpace.Lipschitz
import Theorems.Thm_FunctionalInequalities_Analysis_HasWeakDerivAlong_congr_ae_408915f
import Theorems.Thm_FunctionalInequalities_Analysis_HasWeakDerivAlong_mul_of_locally_bounded_408915f
import Theorems.Thm_FunctionalInequalities_Analysis_ae_weak_matrix_inverse_derivative_408915f
import Theorems.Thm_FunctionalInequalities_Analysis_exists_weak_hessian_adjugate_derivative_408915f
import Theorems.Thm_FunctionalInequalities_Analysis_hasWeakDerivAlong_exp_neg_of_lipschitz_408915f
import Theorems.Thm_FunctionalInequalities_Probability_Stein_norm_hessianMatrix_entry_le_of_lipschitz_gradient_408915f

section
open MeasureTheory
open FunctionalInequalities.Analysis.BakryEmery
open scoped RealInnerProductSpace ContDiff
noncomputable section HessianEntryBounds
open MeasureTheory
open FunctionalInequalities.Probability.Stein
open scoped RealInnerProductSpace
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Probability
end FunctionalInequalities.Probability
open FunctionalInequalities FunctionalInequalities.Probability
section
namespace FunctionalInequalities.Probability.Stein
end FunctionalInequalities.Probability.Stein
open FunctionalInequalities FunctionalInequalities.Probability FunctionalInequalities.Probability.Stein
private lemma FunctionalInequalities.Probability.Stein.n10_hessian {n : ℕ}
    (u : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    hessianMatrix u x = FunctionalInequalities.Probability.Stein.n10_matrix (fderiv ℝ (gradient u) x) := by
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
private lemma FunctionalInequalities.Probability.Stein.n11b_continuous_hessian_entry {n : ℕ} (i j : Fin n) :
    Continuous
      (fun L : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) =>
        FunctionalInequalities.Probability.Stein.n10_matrix L i j) := by
  let T : EuclideanSpace ℝ (Fin n) ≃L[ℝ]
      StrongDual ℝ (EuclideanSpace ℝ (Fin n)) :=
    (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).toContinuousLinearEquiv
  exact
    (T.continuous.comp (continuous_id.clm_apply continuous_const)).clm_apply
      continuous_const
/-- Measurability of the total coordinate Hessian, without smoothness premises. -/
theorem FunctionalInequalities.Probability.Stein.measurable_hessianMatrix_entry {n : ℕ}
    (u : EuclideanSpace ℝ (Fin n) → ℝ) (i j : Fin n) :
    Measurable (fun x => hessianMatrix u x i j) := by
  simpa only [n10_hessian, Function.comp_def] using
    (n11b_continuous_hessian_entry i j).measurable.comp
      (measurable_fderiv ℝ (gradient u))
end
end
end
end HessianEntryBounds
end

section
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
end
end
end LN10AInverseHessianDivergence
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
theorem FunctionalInequalities.Analysis.memLp_hessian_adjugate_top {n : ℕ}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} {G : NNReal}
    (hG : LipschitzWith G (gradient u)) (i j : Fin n) :
    MemLp (fun x => (hessianMatrix u x).adjugate i j) (⊤ : ENNReal)
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
  obtain ⟨C, hC⟩ := n10_cofactor_bound hG i j
  exact memLp_top_of_bound (n10_measurable_cofactor u i j).aestronglyMeasurable C
    (Filter.Eventually.of_forall hC)
end
end
end WeakHessianAdjugateConsumers
end
end

noncomputable section
section WeakInverseDerivative
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
/-- A Lipschitz log-det representative and the given weak Hessian tensor
produce the explicit weak inverse derivative. This is weak Letwin (2.5), not (2.6). -/
theorem solution {n : ℕ}
    {u F : EuclideanSpace ℝ (Fin n) → ℝ} {G LF : NNReal}
    {T : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → Fin n → ℝ}
    (hG : LipschitzWith G (gradient u)) (hF : LipschitzWith LF F)
    (hdata : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      (FunctionalInequalities.Probability.Stein.hessianMatrix u x).PosDef ∧ Real.log (FunctionalInequalities.Probability.Stein.hessianMatrix u x).det = F x)
    (hT : ∀ k i j : Fin n,
      FunctionalInequalities.Analysis.HasWeakDerivAlong (fun x => FunctionalInequalities.Probability.Stein.hessianMatrix u x i j) (fun x => T x k i j)
        (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
      ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
        MemLp (fun x => T x k i j) 2
          ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) :
    ∀ k i j : Fin n,
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
          ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) := by
  classical
  let H := FunctionalInequalities.Probability.Stein.hessianMatrix u
  let R : EuclideanSpace ℝ (Fin n) → Matrix (Fin n) (Fin n) ℝ := fun x => (H x)⁻¹
  have hbound (a b : Fin n) : MemLp (fun x => H x a b)
      (⊤ : ENNReal) (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    memLp_top_of_bound (FunctionalInequalities.Probability.Stein.measurable_hessianMatrix_entry u a b).aestronglyMeasurable
      (G : ℝ) (Filter.Eventually.of_forall fun x =>
        FunctionalInequalities.Probability.Stein.norm_hessianMatrix_entry_le_of_lipschitz_gradient_408915f hG x a b)
  have hC (k i j : Fin n) := FunctionalInequalities.Analysis.exists_weak_hessian_adjugate_derivative_408915f hbound hT k i j
  choose dc hdc hdc2 using hC
  have hExp : Continuous (fun x => Real.exp (-F x)) := Real.continuous_exp.comp hF.continuous.neg
  have hExpTop (S : Set (EuclideanSpace ℝ (Fin n))) (hS : IsCompact S) :
      MemLp (fun x => Real.exp (-F x)) (⊤ : ENNReal)
        ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) := by
    obtain ⟨C, hC⟩ := hS.exists_bound_of_continuousOn hExp.continuousOn
    exact memLp_top_of_bound hExp.aestronglyMeasurable C
      ((ae_restrict_mem hS.measurableSet).mono fun x hx => hC x hx)
  have hInv (i j : Fin n) : (fun x => R x i j) =ᵐ[
      (volume : Measure (EuclideanSpace ℝ (Fin n)))]
      (fun x => Real.exp (-F x) * (H x).adjugate i j) := by
    filter_upwards [hdata] with x hx
    have hdet : (H x).det = Real.exp (F x) := by
      rw [← hx.2, Real.exp_log hx.1.det_pos]
    simp only [R, Matrix.inv_def, hdet, Ring.inverse_eq_inv, Matrix.smul_apply,
      smul_eq_mul, Real.exp_neg]
  have hRtop (i j : Fin n) (S : Set (EuclideanSpace ℝ (Fin n))) (hS : IsCompact S) :
      MemLp (fun x => R x i j) (⊤ : ENNReal)
        ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) :=
    MemLp.ae_eq (ae_restrict_of_ae (hInv i j).symm)
      (((FunctionalInequalities.Analysis.memLp_hessian_adjugate_top hG i j).restrict S).mul' (hExpTop S hS))
  let DR : Fin n → EuclideanSpace ℝ (Fin n) → Matrix (Fin n) (Fin n) ℝ :=
    fun k x => Matrix.of fun a b =>
      (-Real.exp (-F x) * fderiv ℝ F x (EuclideanSpace.basisFun (Fin n) ℝ k)) *
        (H x).adjugate a b + Real.exp (-F x) * dc k a b x
  have hD (k i j : Fin n) :
      FunctionalInequalities.Analysis.HasWeakDerivAlong (fun x => R x i j) (fun x => DR k x i j)
        (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
      ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
        MemLp (fun x => DR k x i j) 2
          ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) := by
    have hs := FunctionalInequalities.Analysis.hasWeakDerivAlong_exp_neg_of_lipschitz_408915f hF
      (EuclideanSpace.basisFun (Fin n) ℝ k)
    have hp := hs.1.mul_of_locally_bounded_408915f (hdc k i j) hExpTop
      (fun S _ => (FunctionalInequalities.Analysis.memLp_hessian_adjugate_top hG i j).restrict S) hs.2 (hdc2 k i j)
    exact ⟨hp.1.congr_ae_408915f (hInv i j).symm Filter.EventuallyEq.rfl, hp.2⟩
  have hRA : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))), R x * H x = 1 := by
    filter_upwards [hdata] with x hx
    exact Matrix.nonsing_inv_mul (H x) (isUnit_iff_ne_zero.mpr (ne_of_gt hx.1.det_pos))
  intro k i j
  let DT : EuclideanSpace ℝ (Fin n) → Matrix (Fin n) (Fin n) ℝ :=
    fun x => Matrix.of fun a b => T x k a b
  have hEq := FunctionalInequalities.Analysis.ae_weak_matrix_inverse_derivative_408915f (A := H) (R := R) (DA := DT) (DR := DR k)
    (fun a b => (hT k a b).1) (fun a b => (hD k a b).1)
    (fun a b S _ => (hbound a b).restrict S) hRtop
    (fun a b => (hT k a b).2) (fun a b => (hD k a b).2) hRA
  have hij : (fun x => DR k x i j) =ᵐ[(volume : Measure (EuclideanSpace ℝ (Fin n)))]
      (fun x => -((R x * DT x * R x) i j)) := by
    filter_upwards [hEq] with x hx
    simpa only [Matrix.neg_apply] using congrArg (fun M => M i j) hx
  refine ⟨(hD k i j).1.congr_ae_408915f Filter.EventuallyEq.rfl hij, ?_, hRtop i j⟩
  intro S hS
  exact MemLp.ae_eq (ae_restrict_of_ae hij) ((hD k i j).2 S hS)
