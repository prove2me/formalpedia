-- Prove2me | solution 1 for DedekindZeta.ConeRadialReduction.smul_inv_mixedSpace
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:40:58.070501+00:00
-- url     : https://prove2.me/submissions/51a83c9d-beca-4574-b35c-714e3c7dc7cb

import Mathlib
import Definitions.Def_DedekindZeta_Statements
import Definitions.Def_DedekindZeta_MellinPrinciple
import Definitions.Def_DedekindZeta_GammaIntegral
import Definitions.Def_DedekindZeta_ConeRadialReduction
import Theorems.Thm_DedekindZeta_ConeRadialReduction_mem_normEqOneSurface
import Theorems.Thm_DedekindZeta_Theta_gaussVSchwartz_apply
import Theorems.Thm_DedekindZeta_Theta_mixedGaussianSchwartz_apply
attribute [local simp] DedekindZeta.Theta.gaussVSchwartz_apply
attribute [local simp] DedekindZeta.Theta.mixedGaussianSchwartz_apply


attribute [local simp] DedekindZeta.ConeRadialReduction.mem_normEqOneSurface

set_option autoImplicit true
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
open MeasureTheory Module
open scoped Real ENNReal nonZeroDivisors
open DedekindZeta DedekindZeta.ConeRadialReduction
variable (K : Type*) [Field K] [NumberField K]
variable {K}
omit [NumberField K]
namespace DedekindZeta.ConeRadialReduction
theorem _root_.solution (c : ℝ) (x : mixedSpace K) :
    (c • x)⁻¹ = c⁻¹ • x⁻¹ := by
  ext i <;>
    simp [Pi.smul_apply, Pi.inv_apply, Complex.ofReal_inv,
      Complex.real_smul, smul_eq_mul, mul_comm]
end DedekindZeta.ConeRadialReduction
