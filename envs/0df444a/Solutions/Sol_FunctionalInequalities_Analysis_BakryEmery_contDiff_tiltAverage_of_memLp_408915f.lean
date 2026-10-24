-- Prove2me | solution 1 for FunctionalInequalities.Analysis.BakryEmery.contDiff_tiltAverage_of_memLp_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T14:42:08.56731+00:00
-- url     : https://prove2.me/submissions/9f32817f-e890-45cb-a1b5-6ba47c1c2036

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Laplacian
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_SquareIntegrable
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Coefficients
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Coordinate
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Multilinear
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Symmetrization
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.Multilinear.Curry
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Measure.Tilted
import Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_integrable_exp_mul_norm_of_memLp_408915f

noncomputable section
open MeasureTheory Filter Topology FunctionalInequalities.Analysis.Tensor
open scoped RealInnerProductSpace ContDiff ENNReal
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
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
section IntegralCalculus
omit [CompleteSpace E]
omit [FiniteDimensional ℝ E] in
private lemma FunctionalInequalities.Analysis.BakryEmery.integrable_exp_inner_of_all_exp (μ : Measure E) [IsFiniteMeasure μ]
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) μ) (z : E) :
    Integrable (fun x => Real.exp ⟪z, x⟫) μ := by
  have hmeas : AEStronglyMeasurable (fun x : E => Real.exp ⟪z, x⟫) μ :=
    (Real.continuous_exp.comp (continuous_const.inner continuous_id)).aestronglyMeasurable
  have hbound : ∀ᵐ x ∂μ, ‖Real.exp ⟪z, x⟫‖ ≤ Real.exp (‖z‖ * ‖x‖) := by
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    exact le_trans (le_abs_self _) (abs_real_inner_le_norm z x)
  exact (hexp ‖z‖).mono' hmeas hbound
namespace FunctionalInequalities.Analysis.BakryEmery
end FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities.Analysis.BakryEmery in
/-- Tilt averages of square-integrable functions are smooth. -/
theorem solution (μ : Measure E) [IsFiniteMeasure μ] [NeZero μ]
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) μ) {f : E → ℝ} (hf : MemLp f 2 μ) :
    ContDiff ℝ ∞ (FunctionalInequalities.Analysis.BakryEmery.tiltAverage μ f) := by
    let N : E → ℝ := fun z => ∫ x, Real.exp ⟪z, x⟫ • f x ∂μ
    let D : E → ℝ := fun z => ∫ x, Real.exp ⟪z, x⟫ • (1 : ℝ) ∂μ
    have hN : ContDiff ℝ ∞ N := by
      dsimp [N]
      exact FunctionalInequalities.Analysis.BakryEmery.contDiff_integral_exp_inner_smul_of_integrable
        (μ := μ) (g := f) hf.aestronglyMeasurable
        (fun r => FunctionalInequalities.Analysis.BakryEmery.integrable_exp_mul_norm_of_memLp_408915f μ hexp hf r)
    have hD : ContDiff ℝ ∞ D := by
      dsimp [D]
      exact FunctionalInequalities.Analysis.BakryEmery.contDiff_integral_exp_inner_smul_of_integrable
        (μ := μ) (g := (1 : E → ℝ))
        stronglyMeasurable_const.aestronglyMeasurable
        (fun r => by simpa using hexp r)
    have hDpos : ∀ z : E, 0 < D z := by
      intro z
      dsimp [D]
      simpa using
        (integral_exp_pos (μ := μ) (f := fun x : E => ⟪z, x⟫)
          (hf := integrable_exp_inner_of_all_exp μ hexp z))
    have hDinv : ContDiff ℝ ∞ (fun z => (D z)⁻¹) :=
      hD.inv (fun z => ne_of_gt (hDpos z))
    have hmul : ContDiff ℝ ∞ (fun z => (D z)⁻¹ * N z) := by
      convert hDinv.smul hN using 1
      ext z
      rfl
    have htilt : FunctionalInequalities.Analysis.BakryEmery.tiltAverage μ f = (fun z => (D z)⁻¹ * N z) := by
      funext z
      simp only [FunctionalInequalities.Analysis.BakryEmery.tiltAverage, MeasureTheory.integral_tilted, FunctionalInequalities.Analysis.BakryEmery.expTilt, D, N,
        div_eq_mul_inv, smul_eq_mul]
      have hden :
          (∫ x : E, Real.exp ⟪z, x⟫ * 1 ∂μ) =
            ∫ x : E, Real.exp ⟪z, x⟫ ∂μ := by
        simp
      rw [hden]
      calc
        ∫ x : E, Real.exp ⟪z, x⟫ *
            (∫ x : E, Real.exp ⟪z, x⟫ ∂μ)⁻¹ * f x ∂μ =
            ∫ x : E, (∫ x : E, Real.exp ⟪z, x⟫ ∂μ)⁻¹ •
              (Real.exp ⟪z, x⟫ * f x) ∂μ := by
                apply integral_congr_ae
                filter_upwards with x
                simp only [smul_eq_mul]
                ring
        _ = (∫ x : E, Real.exp ⟪z, x⟫ ∂μ)⁻¹ •
            ∫ x : E, Real.exp ⟪z, x⟫ * f x ∂μ := by
              rw [integral_smul]
        _ = (∫ x : E, Real.exp ⟪z, x⟫ ∂μ)⁻¹ *
            ∫ x : E, Real.exp ⟪z, x⟫ * f x ∂μ := by
              simp [smul_eq_mul]
    rw [htilt]
    exact hmul
