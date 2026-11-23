-- Prove2me | solution 1 for DedekindZeta.ConeRadialReduction.mapsTo_radialMap_closure_normEqOneSurface
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:40:46.60257+00:00
-- url     : https://prove2.me/submissions/a69494ce-604f-43db-9f6a-7220b37746f6

import Mathlib
import Definitions.Def_DedekindZeta_Statements
import Definitions.Def_DedekindZeta_MellinPrinciple
import Definitions.Def_DedekindZeta_GammaIntegral
import Definitions.Def_DedekindZeta_ConeRadialReduction
import Theorems.Thm_DedekindZeta_ConeRadialReduction_mem_normEqOneSurface
import Theorems.Thm_DedekindZeta_ConeRadialReduction_norm_radialMap
import Theorems.Thm_DedekindZeta_ConeRadialReduction_closure_normEqOneSurface_subset
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
variable (K)
namespace DedekindZeta.ConeRadialReduction
theorem _root_.solution (r : ℝ) (hr : 0 < r) :
    Set.MapsTo (radialMap K r) (closure (normEqOneSurface K))
      {x : mixedSpace K | mixedEmbedding.norm x ≠ 0} := by
  intro x hx
  have hx1 : mixedEmbedding.norm x = 1 := closure_normEqOneSurface_subset K hx
  simp only [Set.mem_setOf_eq, norm_radialMap r hr x, hx1, mul_one]
  exact hr.ne'
end DedekindZeta.ConeRadialReduction
