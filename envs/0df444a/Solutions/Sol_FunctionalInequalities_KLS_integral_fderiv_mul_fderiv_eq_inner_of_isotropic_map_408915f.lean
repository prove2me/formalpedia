-- Prove2me | solution 1 for FunctionalInequalities.KLS.integral_fderiv_mul_fderiv_eq_inner_of_isotropic_map_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T15:36:58.004735+00:00
-- url     : https://prove2.me/submissions/88ee630f-934e-49cf-aa44-00a7ed90de76

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Bochner_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Gamma
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Laplacian
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Cutoff_SmoothBall
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Lipschitz_Gradient
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_Isotropic
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Covariance_Basic
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Norm
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.Probability.Moments.CovarianceBilin
import Mathlib.Tactic.NoncommRing
import Mathlib.Topology.MetricSpace.Lipschitz

noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.KLS
end FunctionalInequalities.KLS
open FunctionalInequalities FunctionalInequalities.KLS
variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [MeasurableSpace E] [BorelSpace E]
section Moments
variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
/-- For an isotropic law the raw second moments are `∫ ⟪u, x⟫ ⟪v, x⟫ = ⟪u, v⟫`. -/
theorem FunctionalInequalities.KLS.Isotropic.integral_inner_mul_inner
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {ν : ProbabilityMeasure E}
    (hν : Isotropic ν) (u v : E) :
    (∫ x, ⟪u, x⟫ * ⟪v, x⟫ ∂(ν : Measure E)) = ⟪u, v⟫ := by
  calc
    (∫ x, ⟪u, x⟫ * ⟪v, x⟫ ∂(ν : Measure E)) =
        ∫ x, ⟪u, x - ∫ y, id y ∂(ν : Measure E)⟫ *
          ⟪v, x - ∫ y, id y ∂(ν : Measure E)⟫ ∂(ν : Measure E) := by
      simp [hν.mean_zero]
    _ = ProbabilityTheory.covarianceBilin (ν : Measure E) u v := by
      rw [ProbabilityTheory.covarianceBilin_apply hν.memLp_two]
    _ = ⟪u, v⟫ := by
      rw [← Covariance.operator_inner, hν.covariance_identity]
      simp
end Moments
section FiniteDimensional
variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
namespace FunctionalInequalities.KLS
end FunctionalInequalities.KLS
open FunctionalInequalities.KLS in
/-- **Gradient second moments of an isotropic pushforward** (Letwin Lemma 2.3, step 2): if `(∇φ)_* ν` is isotropic then
`∫ (∂_u φ)(∂_v φ) dν = ⟪u, v⟫`. -/
theorem solution
    (ν : ProbabilityMeasure E) {φ : E → ℝ} (hφ : Measurable (gradient φ))
    (hiso : FunctionalInequalities.KLS.Isotropic (ν.map hφ.aemeasurable)) (u v : E) :
    ∫ x, fderiv ℝ φ x u * fderiv ℝ φ x v ∂(ν : Measure E) = ⟪u, v⟫ := by
    have hderiv (x w : E) :
        fderiv ℝ φ x w = ⟪w, gradient φ x⟫ := by
      rw [← toDual_gradient, InnerProductSpace.toDual_apply_apply, real_inner_comm]

    have hmeas :
        AEStronglyMeasurable
          (fun y : E => ⟪u, y⟫ * ⟪v, y⟫)
          ((ν : Measure E).map (gradient φ)) := by
      exact
        ((continuous_const.inner continuous_id).mul
          (continuous_const.inner continuous_id)).aestronglyMeasurable

    calc
      ∫ x, fderiv ℝ φ x u * fderiv ℝ φ x v ∂(ν : Measure E) =
          ∫ x, ⟪u, gradient φ x⟫ * ⟪v, gradient φ x⟫ ∂(ν : Measure E) := by
        apply integral_congr_ae
        filter_upwards [] with x
        rw [hderiv x u, hderiv x v]
      _ = ∫ y, ⟪u, y⟫ * ⟪v, y⟫
            ∂((ν : Measure E).map (gradient φ)) := by
        exact (integral_map hφ.aemeasurable hmeas).symm
      _ = ⟪u, v⟫ := by
        have h := hiso.integral_inner_mul_inner u v
        simp only [ProbabilityMeasure.toMeasure_map] at h
        exact h
