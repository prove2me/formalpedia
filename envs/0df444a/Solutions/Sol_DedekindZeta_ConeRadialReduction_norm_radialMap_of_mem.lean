-- Prove2me | solution 1 for DedekindZeta.ConeRadialReduction.norm_radialMap_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:31:21.188643+00:00
-- url     : https://prove2.me/submissions/cf659963-2c00-4ce3-b926-7737a0baff4d

import Mathlib
import Definitions.Def_DedekindZeta_Statements
import Definitions.Def_DedekindZeta_MellinPrinciple
import Definitions.Def_DedekindZeta_GammaIntegral
import Definitions.Def_DedekindZeta_ConeRadialReduction
import Theorems.Thm_DedekindZeta_ConeRadialReduction_mem_normEqOneSurface
import Theorems.Thm_DedekindZeta_ConeRadialReduction_norm_radialMap
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
namespace DedekindZeta.ConeRadialReduction
theorem _root_.solution (r : ℝ) (hr : 0 < r) {σ : mixedSpace K}
    (hσ : σ ∈ normEqOneSurface K) :
    mixedEmbedding.norm (radialMap K r σ) = r := by
  rw [norm_radialMap r hr σ, (mem_normEqOneSurface.mp hσ).2, mul_one]
end DedekindZeta.ConeRadialReduction
