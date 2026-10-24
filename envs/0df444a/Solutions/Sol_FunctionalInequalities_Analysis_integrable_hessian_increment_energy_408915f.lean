-- Prove2me | solution 1 for FunctionalInequalities.Analysis.integrable_hessian_increment_energy_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T15:18:35.526319+00:00
-- url     : https://prove2.me/submissions/b292f2ae-6e85-4f60-9652-09b77f873d51

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_HessianOperator
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_InverseHessian_Weak
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_WeakHessian
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_AffineMaximum
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Alexandrov
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Legendre
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Proximal
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
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_BrunnMinkowski
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Line_BrunnMinkowski
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
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Calculus.TaylorIntegral
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Convex.Deriv
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
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.Normed.Affine.Convex
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Star
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.SpecificCodomains.Pi
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Algebra.Group.Matrix
import Mathlib.Topology.Algebra.MetricSpace.Lipschitz
import Mathlib.Topology.Algebra.Support
import Mathlib.Topology.EMetricSpace.Lipschitz
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.Semicontinuity.Basic
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

noncomputable section
open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace
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
/-- The squared shifted Hessian-increment density is integrable
against the continuous compact weight. No C2 or given integrability is assumed. -/
theorem solution {n : ℕ}
    {u η : EuclideanSpace ℝ (Fin n) → ℝ}
    (hu : Continuous u) {G : NNReal} (hG : LipschitzWith G (gradient u))
    (hη : Continuous η) (hηc : HasCompactSupport η)
    (h : EuclideanSpace ℝ (Fin n)) :
    Integrable (fun x => η x *
      ((∑ i, ∑ j, (FunctionalInequalities.Probability.Stein.hessianMatrix u (x + h) - FunctionalInequalities.Probability.Stein.hessianMatrix u x) i j ^ 2) +
       ∑ i, ∑ j, (FunctionalInequalities.Probability.Stein.hessianMatrix u (x - h) - FunctionalInequalities.Probability.Stein.hessianMatrix u x) i j ^ 2) *
      Real.exp (-u x)) (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
  let w : EuclideanSpace ℝ (Fin n) → ℝ := fun x => η x * Real.exp (-u x)
  have hwc : Continuous w :=
    hη.mul (Real.continuous_exp.comp hu.neg)
  have hws : HasCompactSupport w := hηc.mul_right
  have hw : Integrable w (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    hwc.integrable_of_hasCompactSupport hws
  have hentry
      (T : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
      (hT : Continuous T) (i j : Fin n) :
      Integrable
        (fun x => (FunctionalInequalities.Probability.Stein.hessianMatrix u (T x) i j - FunctionalInequalities.Probability.Stein.hessianMatrix u x i j) ^ 2 * w x)
        (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    have hm := FunctionalInequalities.Probability.Stein.measurable_hessianMatrix_entry u i j
    have hmd :
        Measurable (fun x => FunctionalInequalities.Probability.Stein.hessianMatrix u (T x) i j - FunctionalInequalities.Probability.Stein.hessianMatrix u x i j) :=
      (hm.comp hT.measurable).sub hm
    have hms :
        Measurable
          (fun x => (FunctionalInequalities.Probability.Stein.hessianMatrix u (T x) i j - FunctionalInequalities.Probability.Stein.hessianMatrix u x i j) ^ 2) := by
      simp only [pow_two]
      exact hmd.mul hmd
    apply hw.bdd_mul hms.aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro x
    have hb :
        ‖FunctionalInequalities.Probability.Stein.hessianMatrix u (T x) i j - FunctionalInequalities.Probability.Stein.hessianMatrix u x i j‖ ≤
          (G : ℝ) + (G : ℝ) :=
      calc
        ‖FunctionalInequalities.Probability.Stein.hessianMatrix u (T x) i j - FunctionalInequalities.Probability.Stein.hessianMatrix u x i j‖ ≤
            ‖FunctionalInequalities.Probability.Stein.hessianMatrix u (T x) i j‖ + ‖FunctionalInequalities.Probability.Stein.hessianMatrix u x i j‖ :=
          norm_sub_le _ _
        _ ≤ (G : ℝ) + (G : ℝ) :=
          add_le_add
            (FunctionalInequalities.Probability.Stein.norm_hessianMatrix_entry_le_of_lipschitz_gradient_408915f hG (T x) i j)
            (FunctionalInequalities.Probability.Stein.norm_hessianMatrix_entry_le_of_lipschitz_gradient_408915f hG x i j)
    exact
      (norm_pow _ 2).le.trans
        (pow_le_pow_left₀ (norm_nonneg _) hb 2)
  have hsum
      (T : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
      (hT : Continuous T) :
      Integrable
        (fun x => ∑ i, ∑ j,
          (FunctionalInequalities.Probability.Stein.hessianMatrix u (T x) i j - FunctionalInequalities.Probability.Stein.hessianMatrix u x i j) ^ 2 * w x)
        (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    integrable_finsetSum Finset.univ fun i _ =>
      integrable_finsetSum Finset.univ fun j _ => hentry T hT i j
  have hp := hsum (fun x => x + h) (continuous_id.add continuous_const)
  have hm := hsum (fun x => x - h) (continuous_id.sub continuous_const)
  apply (hp.add hm).congr
  apply Filter.Eventually.of_forall
  intro x
  change
    (∑ i, ∑ j,
      (FunctionalInequalities.Probability.Stein.hessianMatrix u (x + h) i j - FunctionalInequalities.Probability.Stein.hessianMatrix u x i j) ^ 2 * w x) +
    (∑ i, ∑ j,
      (FunctionalInequalities.Probability.Stein.hessianMatrix u (x - h) i j - FunctionalInequalities.Probability.Stein.hessianMatrix u x i j) ^ 2 * w x) =
    η x *
      ((∑ i, ∑ j, (FunctionalInequalities.Probability.Stein.hessianMatrix u (x + h) - FunctionalInequalities.Probability.Stein.hessianMatrix u x) i j ^ 2) +
       ∑ i, ∑ j, (FunctionalInequalities.Probability.Stein.hessianMatrix u (x - h) - FunctionalInequalities.Probability.Stein.hessianMatrix u x) i j ^ 2) *
      Real.exp (-u x)
  simp only [← Finset.sum_mul, Matrix.sub_apply]
  dsimp only [w]
  ring
