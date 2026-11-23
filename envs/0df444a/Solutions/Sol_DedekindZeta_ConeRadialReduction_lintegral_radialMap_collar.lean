-- Prove2me | solution 1 for DedekindZeta.ConeRadialReduction.lintegral_radialMap_collar
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:32:54.101042+00:00
-- url     : https://prove2.me/submissions/344e2277-0921-4673-bbb3-c18469f326f2

import Mathlib
import Definitions.Def_DedekindZeta_Statements
import Definitions.Def_DedekindZeta_MellinPrinciple
import Definitions.Def_DedekindZeta_GammaIntegral
import Definitions.Def_DedekindZeta_ConeRadialReduction
import Theorems.Thm_DedekindZeta_ConeRadialReduction_mem_normEqOneSurface
import Theorems.Thm_DedekindZeta_ConeRadialReduction_norm_radialMap
import Theorems.Thm_DedekindZeta_ConeRadialReduction_radialMap_mem_cone
import Theorems.Thm_DedekindZeta_ConeRadialReduction_radialMap_radialMap
import Theorems.Thm_DedekindZeta_ConeRadialReduction_lintegral_radialMap_mixedMulHaar
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
theorem _root_.solution (h : mixedSpace K → ℝ≥0∞) (hh : Measurable h)
    {t : ℝ} (ht : 0 < t) :
    ∫⁻ x in (mixedEmbedding.fundamentalCone K ∩
          {x | mixedEmbedding.norm x ∈ Set.Ioc 1 (Real.exp 1)}),
        h (radialMap K t x) ∂(DedekindZeta.mixedMulHaar K)
      = ∫⁻ y in (mixedEmbedding.fundamentalCone K ∩
            {y | mixedEmbedding.norm y ∈ Set.Ioc t (Real.exp 1 * t)}),
          h y ∂(DedekindZeta.mixedMulHaar K) := by
  set C : Set (mixedSpace K) := mixedEmbedding.fundamentalCone K ∩
      {x | mixedEmbedding.norm x ∈ Set.Ioc 1 (Real.exp 1)} with hC
  set Ct : Set (mixedSpace K) := mixedEmbedding.fundamentalCone K ∩
      {y | mixedEmbedding.norm y ∈ Set.Ioc t (Real.exp 1 * t)} with hCt
  have hC_meas : MeasurableSet C :=
    (measurableSet_fundamentalCone K).inter
      ((mixedEmbedding.continuous_norm K).measurable measurableSet_Ioc)
  have hCt_meas : MeasurableSet Ct :=
    (measurableSet_fundamentalCone K).inter
      ((mixedEmbedding.continuous_norm K).measurable measurableSet_Ioc)
  -- `radialMap K t x ∈ C_t ↔ x ∈ C`.
  have hiff : ∀ x, radialMap K t x ∈ Ct ↔ x ∈ C := by
    intro x
    rw [hCt, hC]
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, norm_radialMap t ht x, Set.mem_Ioc]
    constructor
    · rintro ⟨hcone, hlo, hhi⟩
      refine ⟨?_, ?_, ?_⟩
      · have h1 := radialMap_mem_cone t⁻¹ (inv_pos.mpr ht) hcone
        rw [radialMap_radialMap _ _ (inv_pos.mpr ht).le ht.le,
          inv_mul_cancel₀ ht.ne'] at h1
        simpa [radialMap, Real.one_rpow] using h1
      · exact lt_of_mul_lt_mul_left (by rwa [mul_one]) ht.le
      · exact le_of_mul_le_mul_left (by rwa [mul_comm (Real.exp 1) t] at hhi) ht
    · rintro ⟨hcone, hlo, hhi⟩
      refine ⟨radialMap_mem_cone t ht hcone, ?_, ?_⟩
      · have := mul_lt_mul_of_pos_left hlo ht
        rwa [mul_one] at this
      · have := mul_le_mul_of_nonneg_left hhi ht.le
        rwa [mul_comm t (Real.exp 1)] at this
  rw [← lintegral_indicator hC_meas, ← lintegral_indicator hCt_meas]
  have hpt : (fun x => C.indicator (fun x => h (radialMap K t x)) x)
      = fun x => Ct.indicator h (radialMap K t x) := by
    classical
    funext x
    rw [Set.indicator_apply, Set.indicator_apply]
    by_cases hx : x ∈ C
    · rw [if_pos hx, if_pos ((hiff x).mpr hx)]
    · rw [if_neg hx, if_neg (fun hc => hx ((hiff x).mp hc))]
  rw [hpt]
  exact lintegral_radialMap_mixedMulHaar (Ct.indicator h) (hh.indicator hCt_meas) ht
end DedekindZeta.ConeRadialReduction
