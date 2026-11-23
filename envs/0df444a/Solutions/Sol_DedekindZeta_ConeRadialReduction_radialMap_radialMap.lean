-- Prove2me | solution 1 for DedekindZeta.ConeRadialReduction.radialMap_radialMap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:27:29.613801+00:00
-- url     : https://prove2.me/submissions/2179b362-4bc8-47e4-8557-16940da4c631

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
theorem _root_.solution (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (x : mixedSpace K) :
    radialMap K a (radialMap K b x) = radialMap K (a * b) x := by
  simp only [radialMap, smul_smul, ← Real.mul_rpow ha hb]
end DedekindZeta.ConeRadialReduction
