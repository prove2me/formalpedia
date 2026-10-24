-- Prove2me | solution 1 for FunctionalInequalities.Analysis.BakryEmery.taylorTensor_one_apply_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T14:50:55.05217+00:00
-- url     : https://prove2.me/submissions/a3c52b3b-3354-4f9d-aa62-820780215569

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Laplacian
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_Local
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_LocalDerivatives
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
import Mathlib.Probability.Moments.IntegrableExpMul
import Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_contDiff_tiltAverage_of_memLp_408915f
import Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_integrable_exp_mul_norm_of_memLp_408915f

section
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
omit [FiniteDimensional ℝ E] [BorelSpace E] in
/-- `F_f(z) · ∫ e^{⟪z,x⟫} dμ = ∫ e^{⟪z,x⟫} f(x) dμ` whenever `∫ e^{⟪z,x⟫} dμ ≠ 0`. -/
theorem FunctionalInequalities.Analysis.BakryEmery.tiltAverage_mul_integral_exp (μ : Measure E) (f : E → ℝ) (z : E)
    (hz : (∫ x, Real.exp ⟪z, x⟫ ∂μ) ≠ 0) :
    tiltAverage μ f z * ∫ x, Real.exp ⟪z, x⟫ ∂μ = ∫ x, Real.exp ⟪z, x⟫ * f x ∂μ := by
    rw [tiltAverage, expTilt, integral_tilted]
    simp only [smul_eq_mul]
    simp_rw [div_mul_eq_mul_div]
    rw [integral_div]
    exact div_mul_cancel₀ _ hz
end IntegralCalculus
end
end
end
end
end

open MeasureTheory Filter Topology
open scoped RealInnerProductSpace ContDiff
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
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
namespace FunctionalInequalities.Analysis.BakryEmery
end FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities.Analysis.BakryEmery in
/-- **The first Taylor tensor is the centered first moment**: for `f ∈ L²(μ)`,
`T_1 f (w) = ∫ ⟪w, x⟫ f(x) dμ − (∫ f dμ) ∫ ⟪w, x⟫ dμ` (BKL p. 30, the `d = 1` coefficient). -/
theorem solution (μ : Measure E) [IsProbabilityMeasure μ]
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) μ) {f : E → ℝ}
    (hf : MemLp f 2 μ) (w : E) :
    FunctionalInequalities.Analysis.BakryEmery.taylorTensor μ f 1 (fun _ => w) =
      (∫ x, ⟪w, x⟫ * f x ∂μ) - (∫ x, f x ∂μ) * ∫ x, ⟪w, x⟫ ∂μ := by
    let A : E → ℝ := FunctionalInequalities.Analysis.BakryEmery.tiltAverage μ f
    let Z : E → ℝ := fun z => ∫ x, Real.exp ⟪z, x⟫ ∂μ
    let N : E → ℝ := fun z => ∫ x, Real.exp ⟪z, x⟫ • f x ∂μ
    have hint (z : E) : Integrable (fun x => Real.exp ⟪z, x⟫) μ := by
      exact (hexp ‖z‖).mono' (by fun_prop) (by
        filter_upwards [] with x
        rw [Real.norm_of_nonneg (Real.exp_pos _).le]
        exact Real.exp_le_exp.mpr (real_inner_le_norm z x))
    have hprod : (fun z => A z * Z z) = N := by
      funext z
      simpa [A, Z, N, smul_eq_mul] using
        (FunctionalInequalities.Analysis.BakryEmery.tiltAverage_mul_integral_exp μ f z
          (integral_exp_pos (hint z)).ne')
    have hA : ContDiff ℝ ∞ A := by
      simpa [A] using (FunctionalInequalities.Analysis.BakryEmery.contDiff_tiltAverage_of_memLp_408915f μ hexp hf)
    have hZ : ContDiff ℝ ∞ Z := by
      simpa [Z, smul_eq_mul, mul_one] using
        (FunctionalInequalities.Analysis.BakryEmery.contDiff_integral_exp_inner_smul_of_integrable μ
          (g := fun _ : E => (1 : ℝ))
          (Measurable.aestronglyMeasurable measurable_const)
          (by simpa using hexp))
    have hN : ContDiff ℝ ∞ N := by
      simpa [N, smul_eq_mul] using
        (FunctionalInequalities.Analysis.BakryEmery.contDiff_integral_exp_inner_smul_of_integrable μ
          (g := f) hf.1
          (FunctionalInequalities.Analysis.BakryEmery.integrable_exp_mul_norm_of_memLp_408915f μ hexp hf))
    have hA' : DifferentiableAt ℝ A 0 := hA.differentiable (by simp) 0
    have hZ' : DifferentiableAt ℝ Z 0 := hZ.differentiable (by simp) 0
    have hfun : (A * Z : E → ℝ) = (fun z => A z * Z z) := by
      funext z
      rfl
    have hprod' :
        fderiv ℝ N 0 =
          A 0 • fderiv ℝ Z 0 + Z 0 • fderiv ℝ A 0 := by
      calc
        fderiv ℝ N 0 =
            fderiv ℝ (fun z => A z * Z z) 0 := by
              rw [hprod]
        _ = A 0 • fderiv ℝ Z 0 + Z 0 • fderiv ℝ A 0 := by
          rw [← hfun]
          exact (hA'.hasFDerivAt.mul hZ'.hasFDerivAt).fderiv
    have hprodw :
        fderiv ℝ N 0 w =
          A 0 * fderiv ℝ Z 0 w + Z 0 * fderiv ℝ A 0 w := by
      simpa only [add_apply, smul_apply, smul_eq_mul] using
        congrArg (fun L : E →L[ℝ] ℝ => L w) hprod'
    have hZw :
        fderiv ℝ Z 0 w = ∫ x, ⟪w, x⟫ ∂μ := by
      calc
        fderiv ℝ Z 0 w =
            iteratedFDeriv ℝ 1 Z 0 (fun _ => w) := by
              rw [iteratedFDeriv_one_apply]
        _ = ∫ x, ⟪w, x⟫ ∂μ := by
          dsimp [Z]
          simpa [real_inner_comm] using
            (FunctionalInequalities.Analysis.BakryEmery.iteratedFDeriv_laplace_zero μ (by norm_num : (0 : ℝ) < 1)
              (hexp 1) 1 (fun _ => w))
    have hgi :
        ∀ t : ℝ, t < 1 →
          Integrable (fun x => Real.exp (t * ‖x‖) * ‖f x‖) μ :=
      fun t _ => FunctionalInequalities.Analysis.BakryEmery.integrable_exp_mul_norm_of_memLp_408915f μ hexp hf t
    have hNw :
        fderiv ℝ N 0 w = ∫ x, ⟪w, x⟫ * f x ∂μ := by
      calc
        fderiv ℝ N 0 w =
            iteratedFDeriv ℝ 1 N 0 (fun _ => w) := by
              rw [iteratedFDeriv_one_apply]
        _ = ∫ x, (Real.exp ⟪0, x⟫ *
                ∏ j : Fin 1, ⟪x, w⟫) • f x ∂μ := by
          dsimp [N]
          exact FunctionalInequalities.Analysis.BakryEmery.iteratedFDeriv_weightedExp_integral_of_lt μ
            (g := f) hf.1 hgi 1 0 (by simp) (fun _ => w)
        _ = ∫ x, ⟪w, x⟫ * f x ∂μ := by
          simp [smul_eq_mul, real_inner_comm]
    have hA0 : A 0 = ∫ x, f x ∂μ := by
      simp [A, FunctionalInequalities.Analysis.BakryEmery.tiltAverage, FunctionalInequalities.Analysis.BakryEmery.expTilt]
    have hZ0 : Z 0 = 1 := by
      simp [Z]
    simp only [FunctionalInequalities.Analysis.BakryEmery.taylorTensor, Nat.factorial_one, Nat.cast_one, inv_one, one_smul]
    rw [iteratedFDeriv_one_apply]
    change fderiv ℝ A 0 w =
      (∫ x, ⟪w, x⟫ * f x ∂μ) -
        (∫ x, f x ∂μ) * ∫ x, ⟪w, x⟫ ∂μ
    rw [hNw, hA0, hZ0, hZw] at hprodw
    linarith
