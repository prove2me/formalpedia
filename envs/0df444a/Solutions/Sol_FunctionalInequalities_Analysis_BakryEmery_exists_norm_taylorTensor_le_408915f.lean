-- Prove2me | solution 1 for FunctionalInequalities.Analysis.BakryEmery.exists_norm_taylorTensor_le_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T14:44:18.948067+00:00
-- url     : https://prove2.me/submissions/1f51f261-aadf-4135-91ba-b25cd1e86f38

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
import Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_iteratedFDeriv_integral_exp_inner_smul_408915f

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
omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
private theorem FunctionalInequalities.Analysis.BakryEmery.tiltExp_memLp_two (μ : Measure E)
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) μ) (r : ℝ) :
    MemLp (fun x => Real.exp (r * ‖x‖)) 2 μ := by
  apply (memLp_two_iff_integrable_sq
    (by fun_prop : Continuous (fun x : E => Real.exp (r * ‖x‖))).aestronglyMeasurable).2
  convert hexp (2 * r) using 1
  funext x
  rw [← Real.exp_nat_mul]
  congr 1
  ring
omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
private theorem FunctionalInequalities.Analysis.BakryEmery.tiltExp_cauchy_schwarz (μ : Measure E)
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) μ)
    {f : E → ℝ} (hf : MemLp f 2 μ) (r : ℝ) :
    (∫ x, Real.exp (r * ‖x‖) * ‖f x‖ ∂μ) ≤
      (eLpNorm (fun x => Real.exp (r * ‖x‖)) 2 μ).toReal * (eLpNorm f 2 μ).toReal := by
  have hw := tiltExp_memLp_two μ hexp r
  have heq :
      (∫ x, Real.exp (r * ‖x‖) * ‖f x‖ ∂μ) =
        ⟪hw.toLp (fun x => Real.exp (r * ‖x‖)), hf.norm.toLp (fun x => ‖f x‖)⟫ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hw.coeFn_toLp, hf.norm.coeFn_toLp] with x hx hfx
    rw [hx, hfx]
    simp [mul_comm]
  rw [heq]
  calc
    ⟪hw.toLp (fun x => Real.exp (r * ‖x‖)), hf.norm.toLp (fun x => ‖f x‖)⟫ ≤
        ‖hw.toLp (fun x => Real.exp (r * ‖x‖))‖ *
          ‖hf.norm.toLp (fun x => ‖f x‖)‖ := real_inner_le_norm _ _
    _ = _ := by rw [Lp.norm_toLp, Lp.norm_toLp, eLpNorm_norm]
omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem FunctionalInequalities.Analysis.BakryEmery.tiltMoment_product_bound (d : ℕ) (h : Fin d → E) (x : E) :
    ‖∏ j, ⟪x, h j⟫‖ ≤ Real.exp ((d : ℝ) * ‖x‖) * ∏ j, ‖h j‖ := by
  classical
  have hx : ‖x‖ ≤ Real.exp ‖x‖ :=
    le_trans (by linarith) (Real.add_one_le_exp ‖x‖)
  calc
    ‖∏ j, ⟪x, h j⟫‖ = ∏ j, ‖⟪x, h j⟫‖ := norm_prod _ _
    _ ≤ ∏ j, (Real.exp ‖x‖ * ‖h j‖) := by
      apply Finset.prod_le_prod
      · intro j hj
        exact norm_nonneg _
      · intro j hj
        exact (norm_inner_le_norm x (h j)).trans
          (mul_le_mul_of_nonneg_right hx (norm_nonneg _))
    _ = Real.exp ((d : ℝ) * ‖x‖) * ∏ j, ‖h j‖ := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
        ← Real.exp_nat_mul]
private theorem FunctionalInequalities.Analysis.BakryEmery.tiltNumerator_deriv_bound (μ : Measure E) [IsFiniteMeasure μ]
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) μ)
    {f : E → ℝ} (hf : MemLp f 2 μ) (d : ℕ) :
    ‖iteratedFDeriv ℝ d (fun z => ∫ x, Real.exp ⟪z, x⟫ • f x ∂μ) 0‖ ≤
      (eLpNorm (fun x => Real.exp ((d : ℝ) * ‖x‖)) 2 μ).toReal *
        (eLpNorm f 2 μ).toReal := by
  classical
  have hgi := integrable_exp_mul_norm_of_memLp_408915f μ hexp hf
  apply ContinuousMultilinearMap.opNorm_le_bound (by positivity)
  intro h
  rw [iteratedFDeriv_integral_exp_inner_smul_408915f μ hf.aestronglyMeasurable hgi d 0 h]
  simp only [inner_zero_left, Real.exp_zero, one_mul, smul_eq_mul]
  calc
    ‖∫ x, (∏ j, ⟪x, h j⟫) * f x ∂μ‖ ≤
        ∫ x, (Real.exp ((d : ℝ) * ‖x‖) * ‖f x‖) * (∏ j, ‖h j‖) ∂μ := by
      apply norm_integral_le_of_norm_le ((hgi d).mul_const _)
      filter_upwards [] with x
      rw [norm_mul]
      calc
        ‖∏ j, ⟪x, h j⟫‖ * ‖f x‖ ≤
            (Real.exp ((d : ℝ) * ‖x‖) * ∏ j, ‖h j‖) * ‖f x‖ :=
          mul_le_mul_of_nonneg_right (tiltMoment_product_bound d h x) (norm_nonneg _)
        _ = _ := by ring
    _ = (∫ x, Real.exp ((d : ℝ) * ‖x‖) * ‖f x‖ ∂μ) * ∏ j, ‖h j‖ := by
      rw [integral_mul_const]
    _ ≤ ((eLpNorm (fun x => Real.exp ((d : ℝ) * ‖x‖)) 2 μ).toReal *
        (eLpNorm f 2 μ).toReal) * ∏ j, ‖h j‖ :=
      mul_le_mul_of_nonneg_right (tiltExp_cauchy_schwarz μ hexp hf d)
        (Finset.prod_nonneg fun _ _ => norm_nonneg _)
namespace FunctionalInequalities.Analysis.BakryEmery
end FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities.Analysis.BakryEmery in
/-- **Continuity of `T_d` on `L²(μ)`**: for a probability measure with all exponential moments,
`‖T_d f‖ ≤ C_d ‖f‖_{L²(μ)}` for every `f ∈ L²(μ)`. -/
theorem solution (μ : Measure E) [IsProbabilityMeasure μ]
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) μ) (d : ℕ) :
    ∃ C : ℝ, ∀ f : E → ℝ, MemLp f 2 μ → ‖FunctionalInequalities.Analysis.BakryEmery.taylorTensor μ f d‖ ≤ C * (eLpNorm f 2 μ).toReal := by
  classical
  let D : E → ℝ := fun z => ∫ x, Real.exp ⟪z, x⟫ ∂μ
  let A : E → ℝ := fun z => (D z)⁻¹
  let B : ℕ → ℝ := fun j => (eLpNorm (fun x : E => Real.exp ((j : ℝ) * ‖x‖)) 2 μ).toReal
  have hD : ContDiff ℝ ∞ D := by
    simpa [D] using FunctionalInequalities.Analysis.BakryEmery.contDiff_integral_exp_inner_smul μ hexp
      (g := fun _ : E => (1 : ℝ)) measurable_const.aestronglyMeasurable
      (M := 1) (k := 0) (by intro x; simp)
  have hDi (z : E) : Integrable (fun x => Real.exp ⟪z, x⟫) μ := by
    refine (hexp ‖z‖).mono' ?_ ?_
    · exact (by fun_prop : Continuous (fun x : E => Real.exp ⟪z, x⟫)).aestronglyMeasurable
    · filter_upwards [] with x
      rw [Real.norm_of_nonneg (Real.exp_pos _).le]
      exact Real.exp_le_exp.mpr (real_inner_le_norm z x)
  have hA : ContDiff ℝ ∞ A :=
    hD.inv (fun z => (integral_exp_pos (hDi z)).ne')
  let C : ℝ := ‖(d.factorial : ℝ)⁻¹‖ *
    ∑ i ∈ Finset.range (d + 1),
      (d.choose i : ℝ) * ‖iteratedFDeriv ℝ i A 0‖ * B (d - i)
  refine ⟨C, ?_⟩
  intro f hf
  let N : E → ℝ := fun z => ∫ x, Real.exp ⟪z, x⟫ • f x ∂μ
  have hN : ContDiff ℝ ∞ N :=
    FunctionalInequalities.Analysis.BakryEmery.contDiff_integral_exp_inner_smul_of_integrable μ hf.aestronglyMeasurable
      (FunctionalInequalities.Analysis.BakryEmery.integrable_exp_mul_norm_of_memLp_408915f μ hexp hf)
  have hformula : FunctionalInequalities.Analysis.BakryEmery.tiltAverage μ f = fun z => A z * N z := by
    funext z
    rw [FunctionalInequalities.Analysis.BakryEmery.tiltAverage, FunctionalInequalities.Analysis.BakryEmery.expTilt, integral_tilted]
    change (∫ x, (Real.exp ⟪z, x⟫ / D z) • f x ∂μ) = A z * N z
    simp_rw [div_eq_mul_inv, mul_comm (Real.exp ⟪z, _⟫), mul_smul]
    rw [integral_smul]
    rfl
  calc
    ‖FunctionalInequalities.Analysis.BakryEmery.taylorTensor μ f d‖ =
        ‖(d.factorial : ℝ)⁻¹‖ * ‖iteratedFDeriv ℝ d (fun z => A z * N z) 0‖ := by
      rw [FunctionalInequalities.Analysis.BakryEmery.taylorTensor, norm_smul, hformula]
    _ ≤ ‖(d.factorial : ℝ)⁻¹‖ *
        ∑ i ∈ Finset.range (d + 1),
          (d.choose i : ℝ) * ‖iteratedFDeriv ℝ i A 0‖ *
            ‖iteratedFDeriv ℝ (d - i) N 0‖ := by
      gcongr
      exact norm_iteratedFDeriv_mul_le hA hN 0
        (n := d) (by exact_mod_cast le_top (a := (d : ℕ∞)))
    _ ≤ ‖(d.factorial : ℝ)⁻¹‖ *
        ∑ i ∈ Finset.range (d + 1),
          (d.choose i : ℝ) * ‖iteratedFDeriv ℝ i A 0‖ *
            (B (d - i) * (eLpNorm f 2 μ).toReal) := by
      gcongr with i hi
      exact tiltNumerator_deriv_bound μ hexp hf (d - i)
    _ = C * (eLpNorm f 2 μ).toReal := by
      dsimp [C]
      simp_rw [← mul_assoc]
      rw [← Finset.sum_mul, mul_assoc]
