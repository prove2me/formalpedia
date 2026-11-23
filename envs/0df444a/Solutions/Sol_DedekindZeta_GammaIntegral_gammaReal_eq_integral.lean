-- Prove2me | solution 1 for DedekindZeta.GammaIntegral.gammaReal_eq_integral
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:26:41.997139+00:00
-- url     : https://prove2.me/submissions/ea954755-7a7f-431a-b50e-504ade35d047

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
    gammaReal s = ∫ t : ℝ, realFactor s t := by
  have hmeas : AEMeasurable (fun x : ℝ => ENNReal.ofReal |x|⁻¹) volume := by
    apply Measurable.aemeasurable
    exact ENNReal.measurable_ofReal.comp ((measurable_id.norm).inv)
  rw [gammaReal,
    integral_withDensity_eq_integral_toReal_smul₀ hmeas
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [realFactor, ENNReal.toReal_ofReal (inv_nonneg.2 (abs_nonneg x))]
end DedekindZeta.GammaIntegral
