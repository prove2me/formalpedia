-- Prove2me | solution 1 for DedekindZeta.ConeRadialReduction.norm_radialMap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:27:19.534461+00:00
-- url     : https://prove2.me/submissions/e5f64b5d-bb11-46d9-ad45-c40a38f92ec1

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
namespace DedekindZeta.ConeRadialReduction
theorem _root_.solution (r : ℝ) (hr : 0 < r) (x : mixedSpace K) :
    mixedEmbedding.norm (radialMap K r x) = r * mixedEmbedding.norm x := by
  have hd : finrank ℚ K ≠ 0 := Module.finrank_pos.ne'
  simp only [radialMap, mixedEmbedding.norm_smul,
    abs_of_pos (Real.rpow_pos_of_pos hr ((finrank ℚ K : ℝ)⁻¹)),
    Real.rpow_inv_natCast_pow hr.le hd]
end DedekindZeta.ConeRadialReduction
