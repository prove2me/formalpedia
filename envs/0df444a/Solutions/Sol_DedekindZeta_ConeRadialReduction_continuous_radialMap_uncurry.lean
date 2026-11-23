-- Prove2me | solution 1 for DedekindZeta.ConeRadialReduction.continuous_radialMap_uncurry
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:27:20.223103+00:00
-- url     : https://prove2.me/submissions/512b5d45-fcb0-4158-924e-44416bb21b4f

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
theorem _root_.solution :
    Continuous (fun p : ℝ × mixedSpace K => radialMap K p.1 p.2) := by
  simp only [radialMap]
  exact ((Real.continuous_rpow_const (by positivity)).comp continuous_fst).smul continuous_snd
end DedekindZeta.ConeRadialReduction
