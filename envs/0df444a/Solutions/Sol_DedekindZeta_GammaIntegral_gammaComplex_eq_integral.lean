-- Prove2me | solution 1 for DedekindZeta.GammaIntegral.gammaComplex_eq_integral
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:27:18.883859+00:00
-- url     : https://prove2.me/submissions/e50ef8ba-ecee-4dbe-9fb7-ece76a1c36c7

import Mathlib
import Definitions.Def_DedekindZeta_Statements
import Definitions.Def_DedekindZeta_Theta
import Definitions.Def_DedekindZeta_GammaIntegral
import Theorems.Thm_DedekindZeta_Theta_gaussVSchwartz_apply
import Theorems.Thm_DedekindZeta_Theta_mixedGaussianSchwartz_apply
attribute [local simp] DedekindZeta.Theta.gaussVSchwartz_apply
attribute [local simp] DedekindZeta.Theta.mixedGaussianSchwartz_apply



set_option autoImplicit true
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
open MeasureTheory
open scoped Real ENNReal
open DedekindZeta DedekindZeta.GammaIntegral
open Classical
variable (K : Type*) [Field K] [NumberField K]
noncomputable section
namespace DedekindZeta.GammaIntegral
theorem _root_.solution (s : ℂ) :
    gammaComplex s = ∫ z : ℂ, complexFactor s z := by
  -- Unfold the `withDensity` and push the density into the integrand.
  have hmeas : AEMeasurable
      (fun z : ℂ => ENNReal.ofReal (2 / Real.pi * (‖z‖ ^ 2)⁻¹)) volume := by
    apply Measurable.aemeasurable
    exact ENNReal.measurable_ofReal.comp
      (measurable_const.mul ((measurable_id.norm.pow_const 2).inv))
  rw [gammaComplex,
    integral_withDensity_eq_integral_toReal_smul₀ hmeas
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  have hnn : 0 ≤ 2 / Real.pi * (‖z‖ ^ 2)⁻¹ :=
    mul_nonneg (div_nonneg (by norm_num) Real.pi_pos.le) (inv_nonneg.2 (sq_nonneg _))
  simp only [complexFactor, ENNReal.toReal_ofReal hnn]
end DedekindZeta.GammaIntegral
