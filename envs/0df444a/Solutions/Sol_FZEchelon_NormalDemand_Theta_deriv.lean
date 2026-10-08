-- Prove2me | solution 1 for FZEchelon.NormalDemand.Theta_deriv
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T12:25:51.846505+00:00
-- url     : https://prove2.me/submissions/cbfca7b8-f53f-45ec-a715-25ff7080c003

import Mathlib
import Definitions.Def_FZEchelon_NormalDemand_BivariateNormal

open MeasureTheory ProbabilityTheory in
private lemma pc57_pdf_fun : gaussianPDFReal 0 1
    = fun y => (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(y ^ 2 / 2)) := by
  funext y
  simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
  congr 2
  ring

open MeasureTheory ProbabilityTheory in
private lemma pc57_pdf_cont : Continuous (gaussianPDFReal 0 1) := by
  rw [pc57_pdf_fun]
  fun_prop

open MeasureTheory ProbabilityTheory in
private lemma pc57_pdf_deriv (y : ℝ) :
    HasDerivAt (gaussianPDFReal 0 1) (-y * gaussianPDFReal 0 1 y) y := by
  have h1 : HasDerivAt (fun y : ℝ => -(y ^ 2 / 2)) (-y) y :=
    (((hasDerivAt_pow 2 y).div_const 2).neg).congr_deriv (by norm_num)
  have h2 := (h1.exp).const_mul (Real.sqrt (2 * Real.pi))⁻¹
  rw [pc57_pdf_fun]
  exact h2.congr_deriv (by ring)

open MeasureTheory ProbabilityTheory in
private lemma pc57_real_eq (s : Set ℝ) :
    (gaussianReal 0 1).real s = ∫ v in s, gaussianPDFReal 0 1 v := by
  rw [measureReal_def, gaussianReal_apply_eq_integral 0 one_ne_zero,
    ENNReal.toReal_ofReal (setIntegral_nonneg_of_ae (ae_of_all _ (fun _ => gaussianPDFReal_nonneg _ _ _)))]

open MeasureTheory ProbabilityTheory in
private lemma pc57_cdf_deriv (y : ℝ) :
    HasDerivAt (fun u => cdf (gaussianReal 0 1) u) (gaussianPDFReal 0 1 y) y := by
  have hI : ∀ u, cdf (gaussianReal 0 1) u = ∫ v in Set.Iic u, gaussianPDFReal 0 1 v := by
    intro u; rw [cdf_eq_real, pc57_real_eq]
  have hint : Integrable (gaussianPDFReal 0 1) := integrable_gaussianPDFReal 0 1
  have key : (fun u => cdf (gaussianReal 0 1) u)
      = fun u => cdf (gaussianReal 0 1) 0 + ∫ t in (0:ℝ)..u, gaussianPDFReal 0 1 t := by
    funext u
    rw [← intervalIntegral.integral_Iic_sub_Iic hint.integrableOn hint.integrableOn, hI u, hI 0]
    ring
  rw [key]
  exact ((pc57_pdf_cont.integral_hasStrictDerivAt 0 y).hasDerivAt).const_add
    (cdf (gaussianReal 0 1) 0)

open MeasureTheory ProbabilityTheory Real FZEchelon.NormalDemand in
theorem solution : ∀ x : ℝ, HasDerivAt Theta (stdNormalCDF x) x := by
  intro x
  have hC : HasDerivAt stdNormalCDF (stdNormalPDF x) x := pc57_cdf_deriv x
  have hP : HasDerivAt stdNormalPDF (-x * stdNormalPDF x) x := pc57_pdf_deriv x
  have h := ((hasDerivAt_id x).mul hC).add hP
  have hT : Theta = fun y => id y * stdNormalCDF y + stdNormalPDF y := by
    funext y; rfl
  rw [hT]
  exact h.congr_deriv (by simp)
