-- Prove2me | solution 1 for DedekindZeta.ConeMellinBridge.integrableOn_idealThetaKernel_mul_norm_cpow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:46:51.537743+00:00
-- url     : https://prove2.me/submissions/0a71d309-0953-42a1-9ebb-091301af128b

import Mathlib
import Definitions.Def_DedekindZeta_Statements
import Definitions.Def_DedekindZeta_MellinPrinciple
import Definitions.Def_DedekindZeta_ConeRadialReduction
import Definitions.Def_DedekindZeta_ConeMellinBridge
import Theorems.Thm_DedekindZeta_ConeRadialReduction_mem_normEqOneSurface
import Theorems.Thm_DedekindZeta_Theta_gaussVSchwartz_apply
import Theorems.Thm_DedekindZeta_Theta_idealThetaKernel_eq_mixed
import Theorems.Thm_DedekindZeta_Theta_mixedGaussianSchwartz_apply
import Theorems.Thm_DedekindZeta_integrable_indicator_mixedThetaKernel_mul_norm_cpow
attribute [local simp] DedekindZeta.ConeRadialReduction.mem_normEqOneSurface
attribute [local simp] DedekindZeta.Theta.gaussVSchwartz_apply
attribute [local simp] DedekindZeta.Theta.mixedGaussianSchwartz_apply



set_option autoImplicit true
open MeasureTheory NumberField NumberField.mixedEmbedding
open scoped Real nonZeroDivisors
open DedekindZeta DedekindZeta.ConeMellinBridge
open DedekindZeta.ConeRadialReduction DedekindZeta.MellinPrinciple
variable (K : Type*) [Field K] [NumberField K]
variable {K}
namespace DedekindZeta.ConeMellinBridge
theorem _root_.solution (𝔞 : Ideal (𝓞 K)) {s : ℂ}
    (hs : 1 < s.re) :
    IntegrableOn
      (fun x => Theta.idealThetaKernel K 𝔞 x * (mixedEmbedding.norm x : ℂ) ^ s)
      (mixedEmbedding.fundamentalCone K) (DedekindZeta.mixedMulHaar K) := by
  have h := DedekindZeta.integrable_indicator_mixedThetaKernel_mul_norm_cpow K
    (𝔞 : FractionalIdeal (𝓞 K)⁰ K) s hs
  rw [integrable_indicator_iff (mixedEmbedding.measurableSet_fundamentalCone K)] at h
  simpa only [Theta.idealThetaKernel_eq_mixed] using h
end DedekindZeta.ConeMellinBridge
