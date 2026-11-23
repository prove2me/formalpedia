-- Prove2me | solution 1 for DedekindZeta.ConeRadialReduction.surfaceMeasure_apply_compl_normEqOneSurface
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:31:23.647794+00:00
-- url     : https://prove2.me/submissions/030758cd-6add-43b7-8e06-60245aafe321

import Mathlib
import Definitions.Def_DedekindZeta_Statements
import Definitions.Def_DedekindZeta_MellinPrinciple
import Definitions.Def_DedekindZeta_GammaIntegral
import Definitions.Def_DedekindZeta_ConeRadialReduction
import Theorems.Thm_DedekindZeta_ConeRadialReduction_mem_normEqOneSurface
import Theorems.Thm_DedekindZeta_ConeRadialReduction_measurableSet_normEqOneSurface
import Theorems.Thm_DedekindZeta_ConeRadialReduction_norm_radialMap
import Theorems.Thm_DedekindZeta_ConeRadialReduction_radialMap_mem_cone
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
    surfaceMeasure K (normEqOneSurface K)ᶜ = 0 := by
  -- `radialProj K` is measurable: `x ↦ ((N x)⁻¹) ^ (d⁻¹) • x`, with the scalar
  -- continuous (`d⁻¹ ≥ 0`, so `Real.continuous_rpow_const`) composed with the
  -- measurable `(N ·)⁻¹`.
  have hq : (0 : ℝ) ≤ ((finrank ℚ K : ℝ))⁻¹ := by positivity
  have hscalar : Measurable
      (fun x : mixedSpace K => (mixedEmbedding.norm x)⁻¹ ^ ((finrank ℚ K : ℝ))⁻¹) :=
    (Real.continuous_rpow_const hq).measurable.comp
      ((mixedEmbedding.continuous_norm K).measurable.inv)
  have hmeas : Measurable (radialProj K) := hscalar.smul measurable_id
  rw [surfaceMeasure,
    Measure.map_apply hmeas measurableSet_normEqOneSurface.compl,
    Measure.restrict_apply (hmeas measurableSet_normEqOneSurface.compl)]
  -- The preimage of the complement meets the norm-collar in the empty set:
  -- every collar point has `N x > 1 > 0`, so `radialProj K x` lands in the
  -- norm-1 surface (`norm_radialMap`, scale-invariance of the cone).
  have hempty : (radialProj K ⁻¹' (normEqOneSurface K)ᶜ) ∩
      (mixedEmbedding.fundamentalCone K ∩
        {x | mixedEmbedding.norm x ∈ Set.Ioc 1 (Real.exp 1)}) = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro x ⟨hpre, hx, hN⟩
    have hpos : 0 < mixedEmbedding.norm x := lt_trans one_pos hN.1
    have hcone : radialProj K x ∈ mixedEmbedding.fundamentalCone K :=
      radialMap_mem_cone _ (inv_pos.mpr hpos) hx
    have hnorm : mixedEmbedding.norm (radialProj K x) = 1 := by
      rw [radialProj, norm_radialMap _ (inv_pos.mpr hpos), inv_mul_cancel₀ hpos.ne']
    exact hpre (mem_normEqOneSurface.mpr ⟨hcone, hnorm⟩)
  rw [hempty, measure_empty]
end DedekindZeta.ConeRadialReduction
