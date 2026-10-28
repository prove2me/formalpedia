-- Prove2me | solution 1 for FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.gaussianLaw_inner_sq_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:37:37.360613+00:00
-- url     : https://prove2.me/submissions/6fee0d9a-b3da-4b81-b472-ed181565c493

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Density_GaussianSmoothing_Moments
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_GaussianSmoothing_gaussianLaw_exp_norm_integrable_readable
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_GaussianSmoothing_gaussianLaw_laplace_readable

section
open MeasureTheory ProbabilityTheory Filter Topology
open FunctionalInequalities.Analysis.BakryEmery
open scoped RealInnerProductSpace ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
omit [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.hasFDerivAt_exp_norm_sq_div {s : ℝ} (hs : 0 < s) (z : E) :
    HasFDerivAt (fun w : E => Real.exp (‖w‖ ^ 2 / (4 * s)))
      ((Real.exp (‖z‖ ^ 2 / (4 * s)) / (2 * s)) • innerSL ℝ z) z := by
  have hn : HasFDerivAt (fun w : E => ‖w‖ ^ 2) (2 • innerSL ℝ z) z :=
    (hasStrictFDerivAt_norm_sq z).hasFDerivAt
  have hq : HasFDerivAt (fun w : E => ‖w‖ ^ 2 / (4 * s))
      ((4 * s)⁻¹ • (2 • innerSL ℝ z)) z := by
    convert! hn.const_mul (4 * s)⁻¹ using 1
    funext w
    simp only [div_eq_mul_inv]
    ring
  have h := hq.exp
  convert h using 1
  ext v
  simp only [smul_apply, smul_eq_mul, innerSL_apply_apply]
  field_simp [hs.ne']
  ring
omit [CompleteSpace E] in
/-- `∫ ⟪v,y⟫² dγ_s = ‖v‖²/(2s)`. -/
theorem solution {s : ℝ} (hs : 0 < s) (v : E) :
    (∫ y : E, ⟪v, y⟫ ^ 2 ∂(FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.gaussianLaw s)) = ‖v‖ ^ 2 / (2 * s) := by
  let _ : IsProbabilityMeasure (FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.gaussianLaw (V := E) s) := FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.gaussianLaw_probability hs
  have he : Integrable (fun y : E => Real.exp ((1 : ℝ) * ‖y‖)) (FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.gaussianLaw s) := by
    simpa only [one_mul] using FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.gaussianLaw_exp_norm_integrable_readable (E := E) hs
  let F : E → ℝ := fun z => Real.exp (‖z‖ ^ 2 / (4 * s))
  have hF : ContDiff ℝ 2 F := ((contDiff_norm_sq ℝ).div_const (4 * s)).exp
  have hm := FunctionalInequalities.Analysis.BakryEmery.iteratedFDeriv_laplace_zero (FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.gaussianLaw (V := E) s)
    (by norm_num : (0 : ℝ) < 1) he 2 ![v, v]
  have hfunL : (fun z : E => ∫ y, Real.exp ⟪z, y⟫ ∂(FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.gaussianLaw s)) = F :=
    funext fun z => FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.gaussianLaw_laplace_readable hs z
  rw [hfunL] at hm
  have hprod : (fun y : E => ∏ j : Fin 2, ⟪y, (![v, v] : Fin 2 → E) j⟫) =
      fun y => ⟪v, y⟫ ^ 2 := by
    funext y
    simp [Fin.prod_univ_two, pow_two, real_inner_comm]
  rw [hprod, ← bilinearIteratedFDerivTwo_eq_iteratedFDeriv,
    FunctionalInequalities.Analysis.BakryEmery.bilinearIteratedFDerivTwo_eq_fderiv_apply hF] at hm
  have hfun : (fun z : E => fderiv ℝ F z v) =
      fun z => (F z / (2 * s)) * ⟪v, z⟫ := by
    funext z
    rw [(FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.hasFDerivAt_exp_norm_sq_div hs z).fderiv]
    simp [F, innerSL_apply_apply, real_inner_comm]
  have hzero : HasFDerivAt F (0 : E →L[ℝ] ℝ) 0 := by
    simpa only [F, innerSL, map_zero, smul_zero] using FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.hasFDerivAt_exp_norm_sq_div hs (0 : E)
  have hscaled : HasFDerivAt (fun z => F z / (2 * s)) (0 : E →L[ℝ] ℝ) 0 := by
    convert! hzero.const_mul (2 * s)⁻¹ using 1
    · funext z
      simp only [div_eq_mul_inv]
      ring
    · simp
  have hd : HasFDerivAt (fun z => F z / (2 * s) * ⟪v, z⟫)
      ((1 / (2 * s)) • innerSL ℝ v) 0 := by
    simpa only [Pi.mul_def, coe_innerSL_apply, F, norm_zero, zero_pow (by norm_num : 2 ≠ 0),
      zero_div, Real.exp_zero, inner_zero_right, zero_smul, add_zero] using
      hscaled.mul ((innerSL ℝ v).hasFDerivAt (x := (0 : E)))

  rw [hfun, hd.fderiv] at hm
  simpa only [F, norm_zero, zero_pow (by norm_num : 2 ≠ 0), zero_div, Real.exp_zero,
    inner_zero_right, innerSL_apply_apply, add_apply,
    smul_apply, smul_eq_mul, zero_apply,
    mul_zero, zero_smul, zero_add, add_zero, real_inner_self_eq_norm_sq,
    one_div, one_mul, div_eq_mul_inv, mul_comm] using hm.symm
