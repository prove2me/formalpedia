-- Prove2me | solution 1 for FunctionalInequalities.Analysis.exists_lipschitzWith_weak_fderiv_comp_gradient_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T15:20:26.340041+00:00
-- url     : https://prove2.me/submissions/d6ae241b-f00f-4376-aab8-a65241475c71

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
import Theorems.Thm_FunctionalInequalities_Analysis_HasWeakDerivAlong_congr_ae_408915f
import Theorems.Thm_FunctionalInequalities_Analysis_ae_fderiv_mongeAmpere_exponent_408915f
import Theorems.Thm_FunctionalInequalities_Analysis_exists_lipschitzWith_neg_add_comp_gradient_408915f
import Theorems.Thm_FunctionalInequalities_Analysis_hasWeakDerivAlong_of_lipschitz_408915f

noncomputable section
section WeakCoordinateComposition
open MeasureTheory Set
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
/-- Closed composition of the existing negative-exponent result with the
original Lipschitz potential. A local helper, not a new public interface. -/
private theorem FunctionalInequalities.Analysis.exists_lipschitz_comp_gradient {n : ℕ}
    {u V : EuclideanSpace ℝ (Fin n) → ℝ} {L G : NNReal}
    (hULip : LipschitzWith L u) (hGradLip : LipschitzWith G (gradient u))
    (hV : ContDiff ℝ 1 V) :
    ∃ C : NNReal, LipschitzWith C (fun x => V (gradient u x)) := by
  obtain ⟨LF, hNegCompLip⟩ :=
    exists_lipschitzWith_neg_add_comp_gradient_408915f hULip hGradLip hV
  have hSum := hNegCompLip.add hULip
  change LipschitzWith (LF + L) (fun x => (-u x + V (gradient u x)) + u x) at hSum
  have hCancel : (fun x => (-u x + V (gradient u x)) + u x) =
      (fun x => V (gradient u x)) := by
    funext x
    ring
  rw [hCancel] at hSum
  exact ⟨LF + L, hSum⟩
/-- The scalar derivative bound and compact-local L2 calculation already used
by the accepted Piola-row consumer, with an arbitrary Lipschitz scalar f. -/
private theorem FunctionalInequalities.Analysis.memLp_coordinate_fderiv_of_lipschitz {n : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {C : NNReal}
    (hLip : LipschitzWith C f) (j : Fin n)
    (S : Set (EuclideanSpace ℝ (Fin n))) (hS : IsCompact S) :
    MemLp (fun x => fderiv ℝ f x (EuclideanSpace.basisFun (Fin n) ℝ j))
      2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) := by
  let : IsFiniteMeasure ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) :=
    isFiniteMeasure_restrict.mpr hS.measure_lt_top.ne
  let e := EuclideanSpace.basisFun (Fin n) ℝ
  have hMeas : Measurable (fun x => fderiv ℝ f x (e j)) :=
    (show Continuous (fun A : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ => A (e j)) from
      continuous_id.clm_apply continuous_const).measurable.comp (measurable_fderiv ℝ f)
  have hBound (x : EuclideanSpace ℝ (Fin n)) : ‖fderiv ℝ f x (e j)‖ ≤ (C : ℝ) := by
    have hEval := (fderiv ℝ f x).le_opNorm (e j)
    rw [e.norm_eq_one j, mul_one] at hEval
    exact hEval.trans (norm_fderiv_le_of_lipschitz ℝ hLip)
  exact MemLp.of_bound hMeas.aestronglyMeasurable (C : ℝ)
    (Filter.Eventually.of_forall hBound)
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities.Analysis in
set_option maxHeartbeats 800000 in
/-- Actual weak derivative of a smooth coordinate derivative composed with a
C1 potential's Lipschitz gradient. Supporting component for weak Letwin (2.6). -/
theorem solution {n : ℕ}
    {u W : EuclideanSpace ℝ (Fin n) → ℝ} {L G : NNReal}
    (hu : ContDiff ℝ 1 u) (hULip : LipschitzWith L u)
    (hGradLip : LipschitzWith G (gradient u)) (hW : ContDiff ℝ 2 W)
    (a : Fin n) :
    ∃ C : NNReal,
      LipschitzWith C (fun x => fderiv ℝ W (gradient u x)
        (EuclideanSpace.basisFun (Fin n) ℝ a)) ∧
      ∀ j : Fin n,
        FunctionalInequalities.Analysis.HasWeakDerivAlong
          (fun x => fderiv ℝ W (gradient u x) (EuclideanSpace.basisFun (Fin n) ℝ a))
          (fun x => ∑ b : Fin n, FunctionalInequalities.Probability.Stein.hessianMatrix u x j b * FunctionalInequalities.Probability.Stein.hessianMatrix W (gradient u x) b a)
          (EuclideanSpace.basisFun (Fin n) ℝ j) ∧
        ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
          MemLp
            (fun x => ∑ b : Fin n, FunctionalInequalities.Probability.Stein.hessianMatrix u x j b * FunctionalInequalities.Probability.Stein.hessianMatrix W (gradient u x) b a)
            2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) := by
  let V : EuclideanSpace ℝ (Fin n) → ℝ :=
    fun z => fderiv ℝ W z (EuclideanSpace.basisFun (Fin n) ℝ a)
  have hV : ContDiff ℝ 1 V := by
    change ContDiff ℝ 1
      (fun z => fderiv ℝ W z (EuclideanSpace.basisFun (Fin n) ℝ a))
    exact (hW.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
  obtain ⟨C, hCompLip⟩ :=
    exists_lipschitz_comp_gradient hULip hGradLip hV
  have hCoord (z : EuclideanSpace ℝ (Fin n)) (b : Fin n) :
      fderiv ℝ V z (EuclideanSpace.basisFun (Fin n) ℝ b) =
        FunctionalInequalities.Probability.Stein.hessianMatrix W z b a := by
    change fderiv ℝ
        (fun y => fderiv ℝ W y (EuclideanSpace.basisFun (Fin n) ℝ a)) z
        (EuclideanSpace.basisFun (Fin n) ℝ b) =
      bilinearIteratedFDerivTwo ℝ W z
        (EuclideanSpace.basisFun (Fin n) ℝ b)
        (EuclideanSpace.basisFun (Fin n) ℝ a)
    exact
      (FunctionalInequalities.Analysis.BakryEmery.bilinearIteratedFDerivTwo_eq_fderiv_apply
        hW z (EuclideanSpace.basisFun (Fin n) ℝ b)
        (EuclideanSpace.basisFun (Fin n) ℝ a)).symm
  refine ⟨C, ?_, ?_⟩
  · simpa only [V] using hCompLip
  · intro j
    constructor
    · change FunctionalInequalities.Analysis.HasWeakDerivAlong
        (fun x => V (gradient u x))
        (fun x => ∑ b : Fin n,
          FunctionalInequalities.Probability.Stein.hessianMatrix u x j b * FunctionalInequalities.Probability.Stein.hessianMatrix W (gradient u x) b a)
        (EuclideanSpace.basisFun (Fin n) ℝ j)
      have hExp :=
        FunctionalInequalities.Analysis.ae_fderiv_mongeAmpere_exponent_408915f
          hu hGradLip hV
      have hDiffComp :
          ∀ᵐ x : EuclideanSpace ℝ (Fin n)
            ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
            DifferentiableAt ℝ (fun y => V (gradient u y)) x :=
        hCompLip.ae_differentiableAt (μ := volume)
      have hAe :
          (fun x => fderiv ℝ (fun y => V (gradient u y)) x
              (EuclideanSpace.basisFun (Fin n) ℝ j)) =ᵐ[
                (volume : Measure (EuclideanSpace ℝ (Fin n)))]
            (fun x => ∑ b : Fin n,
              FunctionalInequalities.Probability.Stein.hessianMatrix u x j b * FunctionalInequalities.Probability.Stein.hessianMatrix W (gradient u x) b a) := by
        filter_upwards [hExp, hDiffComp] with x hxExp hxComp
        have hux : DifferentiableAt ℝ u x :=
          hu.differentiable one_ne_zero x
        have hsum :=
          hux.hasFDerivAt.neg.add hxComp.hasFDerivAt
        have hEval := congrArg
          (fun A : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ =>
            A (EuclideanSpace.basisFun (Fin n) ℝ j))
          hsum.fderiv
        have hfun :
            (-u + (fun y => V (gradient u y))) =
              (fun y => -u y + V (gradient u y)) := by
          funext y
          rfl
        rw [hfun] at hEval
        have heval :
            fderiv ℝ (fun y => -u y + V (gradient u y)) x
                (EuclideanSpace.basisFun (Fin n) ℝ j) =
              -fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ j) +
                fderiv ℝ (fun y => V (gradient u y)) x
                  (EuclideanSpace.basisFun (Fin n) ℝ j) := by
          simpa only [neg_apply, add_apply] using hEval
        have hSum :
            (∑ b : Fin n, FunctionalInequalities.Probability.Stein.hessianMatrix u x j b *
              fderiv ℝ V (gradient u x)
                (EuclideanSpace.basisFun (Fin n) ℝ b)) =
              ∑ b : Fin n, FunctionalInequalities.Probability.Stein.hessianMatrix u x j b *
                FunctionalInequalities.Probability.Stein.hessianMatrix W (gradient u x) b a := by
          apply Finset.sum_congr rfl
          intro b _
          rw [hCoord]
        have hxExp' := hxExp j
        rw [hSum] at hxExp'
        linarith [heval, hxExp']
      have hWeakClassical :
          FunctionalInequalities.Analysis.HasWeakDerivAlong
            (fun x => V (gradient u x))
            (fun x => fderiv ℝ (fun y => V (gradient u y)) x
              (EuclideanSpace.basisFun (Fin n) ℝ j))
            (EuclideanSpace.basisFun (Fin n) ℝ j) :=
        FunctionalInequalities.Analysis.hasWeakDerivAlong_of_lipschitz_408915f hCompLip
          (EuclideanSpace.basisFun (Fin n) ℝ j)
      exact hWeakClassical.congr_ae_408915f
        (Filter.Eventually.of_forall (fun x => rfl)) hAe
    · intro S hS
      have hClassicalL2 :=
        memLp_coordinate_fderiv_of_lipschitz hCompLip j S hS
      have hExp :=
        FunctionalInequalities.Analysis.ae_fderiv_mongeAmpere_exponent_408915f
          hu hGradLip hV
      have hDiffComp :
          ∀ᵐ x : EuclideanSpace ℝ (Fin n)
            ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
            DifferentiableAt ℝ (fun y => V (gradient u y)) x :=
        hCompLip.ae_differentiableAt (μ := volume)
      have hAe :
          (fun x => fderiv ℝ (fun y => V (gradient u y)) x
              (EuclideanSpace.basisFun (Fin n) ℝ j)) =ᵐ[
                (volume : Measure (EuclideanSpace ℝ (Fin n)))]
            (fun x => ∑ b : Fin n,
              FunctionalInequalities.Probability.Stein.hessianMatrix u x j b * FunctionalInequalities.Probability.Stein.hessianMatrix W (gradient u x) b a) := by
        filter_upwards [hExp, hDiffComp] with x hxExp hxComp
        have hux : DifferentiableAt ℝ u x :=
          hu.differentiable one_ne_zero x
        have hsum :=
          hux.hasFDerivAt.neg.add hxComp.hasFDerivAt
        have hEval := congrArg
          (fun A : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ =>
            A (EuclideanSpace.basisFun (Fin n) ℝ j))
          hsum.fderiv
        have hfun :
            (-u + (fun y => V (gradient u y))) =
              (fun y => -u y + V (gradient u y)) := by
          funext y
          rfl
        rw [hfun] at hEval
        have heval :
            fderiv ℝ (fun y => -u y + V (gradient u y)) x
                (EuclideanSpace.basisFun (Fin n) ℝ j) =
              -fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ j) +
                fderiv ℝ (fun y => V (gradient u y)) x
                  (EuclideanSpace.basisFun (Fin n) ℝ j) := by
          simpa only [neg_apply, add_apply] using hEval
        have hSum :
            (∑ b : Fin n, FunctionalInequalities.Probability.Stein.hessianMatrix u x j b *
              fderiv ℝ V (gradient u x)
                (EuclideanSpace.basisFun (Fin n) ℝ b)) =
              ∑ b : Fin n, FunctionalInequalities.Probability.Stein.hessianMatrix u x j b *
                FunctionalInequalities.Probability.Stein.hessianMatrix W (gradient u x) b a := by
          apply Finset.sum_congr rfl
          intro b _
          rw [hCoord]
        have hxExp' := hxExp j
        rw [hSum] at hxExp'
        linarith [heval, hxExp']
      have hRestricted :
          (fun x => fderiv ℝ (fun y => V (gradient u y)) x
              (EuclideanSpace.basisFun (Fin n) ℝ j)) =ᵐ[
                (volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S]
            (fun x => ∑ b : Fin n,
              FunctionalInequalities.Probability.Stein.hessianMatrix u x j b * FunctionalInequalities.Probability.Stein.hessianMatrix W (gradient u x) b a) :=
        MeasureTheory.ae_restrict_of_ae hAe
      exact (MeasureTheory.memLp_congr_ae hRestricted).mp hClassicalL2
