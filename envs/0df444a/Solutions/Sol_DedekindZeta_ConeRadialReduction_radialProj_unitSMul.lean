-- Prove2me | solution 1 for DedekindZeta.ConeRadialReduction.radialProj_unitSMul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:41:10.011079+00:00
-- url     : https://prove2.me/submissions/43b57b92-cae5-446c-a8be-58a6cb2d9b85

import Mathlib
import Definitions.Def_DedekindZeta_Statements
import Definitions.Def_DedekindZeta_MellinPrinciple
import Definitions.Def_DedekindZeta_GammaIntegral
import Definitions.Def_DedekindZeta_ConeRadialReduction
import Theorems.Thm_DedekindZeta_ConeRadialReduction_mem_normEqOneSurface
import Theorems.Thm_DedekindZeta_Theta_gaussVSchwartz_apply
import Theorems.Thm_DedekindZeta_Theta_mixedGaussianSchwartz_apply
import Theorems.Thm_DedekindZeta_Theta_norm_unitSMul
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
namespace DedekindZeta.ConeRadialReduction
theorem _root_.solution (u : (𝓞 K)ˣ) (x : mixedSpace K) :
    radialProj K (u • x) = u • radialProj K x := by
  rw [radialProj, radialProj, Theta.norm_unitSMul]
  simp only [radialMap, NumberField.mixedEmbedding.unitSMul_smul]
  exact (Algebra.mul_smul_comm _ _ _).symm
end DedekindZeta.ConeRadialReduction
