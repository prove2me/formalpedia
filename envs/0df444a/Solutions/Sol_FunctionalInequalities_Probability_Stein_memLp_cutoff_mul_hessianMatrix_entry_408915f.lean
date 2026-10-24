-- Prove2me | solution 1 for FunctionalInequalities.Probability.Stein.memLp_cutoff_mul_hessianMatrix_entry_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T15:19:13.76699+00:00
-- url     : https://prove2.me/submissions/9c824066-857b-4804-b702-ae79f6c0a4ec

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_HessianOperator
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_WeakHessian
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Cutoff_SmoothBall
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Lipschitz_Gradient
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Matrix_Positivity
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Operator_Coordinates
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_WeakDerivative_Basic
import Mathlib
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
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Norm
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.SpecificCodomains.Pi
import Mathlib.Topology.MetricSpace.Lipschitz
import Theorems.Thm_FunctionalInequalities_Probability_Stein_norm_hessianMatrix_entry_le_of_lipschitz_gradient_408915f

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
noncomputable section
open MeasureTheory Set
open scoped Topology ContDiff
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
namespace FunctionalInequalities.Probability.Stein
end FunctionalInequalities.Probability.Stein
open FunctionalInequalities.Probability.Stein in
/-- Multiplying a total Hessian entry by a continuous compact cutoff produces
an actual global L2 function for the existing difference-quotient criterion. -/
theorem solution {n : ℕ}
    {u χ : EuclideanSpace ℝ (Fin n) → ℝ} {G : NNReal}
    (hG : LipschitzWith G (gradient u)) (i j : Fin n)
    (hχ : Continuous χ) (hχc : HasCompactSupport χ) :
    MemLp (fun x => χ x * FunctionalInequalities.Probability.Stein.hessianMatrix u x i j) 2
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
  classical
  have hK : IsCompact (tsupport χ) := hχc
  have hKm : MeasurableSet (tsupport χ) :=
    (isClosed_tsupport χ).measurableSet
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hχ.continuousOn
  let : IsFiniteMeasure
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (tsupport χ)) :=
    isFiniteMeasure_restrict.mpr hK.measure_lt_top.ne
  have hlocal : MemLp (fun x => χ x * FunctionalInequalities.Probability.Stein.hessianMatrix u x i j) 2
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (tsupport χ)) := by
    apply MemLp.of_bound
      (hχ.measurable.mul
        (FunctionalInequalities.Probability.Stein.measurable_hessianMatrix_entry u i j)).aestronglyMeasurable
      (C * (G : ℝ))
    exact (ae_restrict_mem hKm).mono fun x hx => by
      calc
        ‖χ x * FunctionalInequalities.Probability.Stein.hessianMatrix u x i j‖ =
            ‖χ x‖ * ‖FunctionalInequalities.Probability.Stein.hessianMatrix u x i j‖ := norm_mul _ _
        _ ≤ ‖χ x‖ * (G : ℝ) :=
          mul_le_mul_of_nonneg_left
            (FunctionalInequalities.Probability.Stein.norm_hessianMatrix_entry_le_of_lipschitz_gradient_408915f hG x i j)
            (norm_nonneg _)
        _ ≤ C * (G : ℝ) :=
          mul_le_mul_of_nonneg_right (hC x hx) (NNReal.coe_nonneg G)
  have heq :
      (tsupport χ).indicator (fun x => χ x * FunctionalInequalities.Probability.Stein.hessianMatrix u x i j) =
        (fun x => χ x * FunctionalInequalities.Probability.Stein.hessianMatrix u x i j) := by
    funext x
    by_cases hx : x ∈ tsupport χ
    · exact Set.indicator_of_mem hx _
    · rw [Set.indicator_of_notMem hx,
        image_eq_zero_of_notMem_tsupport hx, zero_mul]
  rw [← heq]
  exact (memLp_indicator_iff_restrict hKm).mpr hlocal
