-- Prove2me | solution 1 for FunctionalInequalities.KLS.Isotropic.map_linearIsometryEquiv_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T17:41:41.162722+00:00
-- url     : https://prove2.me/submissions/e09fe7f1-8b34-402d-8008-de102aa1ea75

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
/-- **Isotropy from moments**: finite second moment, mean zero and `∫ ⟪u, x⟫⟪v, x⟫ = ⟪u, v⟫`. -/
theorem FunctionalInequalities.KLS.isotropic_of_moments
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (ν : ProbabilityMeasure E) (h2 : MemLp id 2 (ν : Measure E))
    (h0 : ∫ x, x ∂(ν : Measure E) = 0)
    (hcov : ∀ u v : E, ∫ x, ⟪u, x⟫ * ⟪v, x⟫ ∂(ν : Measure E) = ⟪u, v⟫) :
    Isotropic ν := by
    refine ⟨h2, h0, ?_⟩
    apply ContinuousLinearMap.ext
    intro u
    apply ext_inner_right (𝕜 := ℝ)
    intro v
    rw [Covariance.operator_inner]
    rw [ProbabilityTheory.covarianceBilin_apply h2]
    simpa [h0] using hcov u v
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
section LinearIsometry
variable {E F : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
variable [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]
namespace FunctionalInequalities.KLS.Isotropic
end FunctionalInequalities.KLS.Isotropic
open FunctionalInequalities.KLS.Isotropic in
/-- **Isotropy along a linear isometry**.
The `MemLp` step uses `ContinuousLinearMap.comp_memLp'`. -/
theorem solution {ν : ProbabilityMeasure E}
    (hν : FunctionalInequalities.KLS.Isotropic ν) (φ : E ≃ₗᵢ[ℝ] F) :
    FunctionalInequalities.KLS.Isotropic (ν.map φ.continuous.measurable.aemeasurable) := by
    let μ : Measure F := Measure.map φ (ν : Measure E)
    have hmem : MemLp id 2 μ := by
      change MemLp id 2 (Measure.map φ (ν : Measure E))
      apply (memLp_map_measure_iff continuous_id.aestronglyMeasurable
        φ.continuous.measurable.aemeasurable).2
      exact φ.toContinuousLinearMap.comp_memLp' hν.memLp_two
    have hmean : (∫ x, x ∂μ) = 0 := by
      change (∫ x, id x ∂Measure.map φ (ν : Measure E)) = 0
      rw [integral_map φ.continuous.measurable.aemeasurable
        continuous_id.aestronglyMeasurable]
      have hint : Integrable id (ν : Measure E) :=
        hν.memLp_two.integrable (by norm_num)
      calc
        (∫ x, id (φ x) ∂(ν : Measure E)) =
            ∫ x, φ (id x) ∂(ν : Measure E) := by rfl
        _ = φ (∫ x, id x ∂(ν : Measure E)) :=
          φ.toContinuousLinearMap.integral_comp_comm hint
        _ = 0 := by simp [hν.mean_zero]
    refine FunctionalInequalities.KLS.isotropic_of_moments
      (ν.map φ.continuous.measurable.aemeasurable) hmem hmean ?_
    intro u v
    let g : F → ℝ := fun x => ⟪u, x⟫ * ⟪v, x⟫
    have hg : AEStronglyMeasurable g μ := by
      exact
        ((continuous_const.inner continuous_id).mul
          (continuous_const.inner continuous_id)).aestronglyMeasurable
    change (∫ x, g x ∂Measure.map φ (ν : Measure E)) = ⟪u, v⟫
    rw [integral_map φ.continuous.measurable.aemeasurable hg]
    have hu : ∀ x : E, ⟪u, φ x⟫ = ⟪φ.symm u, x⟫ := by
      intro x
      simpa using φ.inner_map_map (φ.symm u) x
    have hv : ∀ x : E, ⟪v, φ x⟫ = ⟪φ.symm v, x⟫ := by
      intro x
      simpa using φ.inner_map_map (φ.symm v) x
    calc
      (∫ x, g (φ x) ∂(ν : Measure E)) =
          ∫ x, ⟪φ.symm u, x⟫ * ⟪φ.symm v, x⟫ ∂(ν : Measure E) := by
        apply integral_congr_ae
        filter_upwards [] with x
        simp only [g, hu, hv]
      _ = ⟪φ.symm u, φ.symm v⟫ :=
        hν.integral_inner_mul_inner (φ.symm u) (φ.symm v)
      _ = ⟪u, v⟫ := by
        simpa only [φ.apply_symm_apply] using
          (φ.inner_map_map (φ.symm u) (φ.symm v)).symm
