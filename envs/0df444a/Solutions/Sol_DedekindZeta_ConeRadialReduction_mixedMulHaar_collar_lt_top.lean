-- Prove2me | solution 1 for DedekindZeta.ConeRadialReduction.mixedMulHaar_collar_lt_top
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:43:45.583475+00:00
-- url     : https://prove2.me/submissions/5ca53874-8f59-4195-bfa1-c88ea2e3b63e

import Mathlib
import Definitions.Def_DedekindZeta_Statements
import Definitions.Def_DedekindZeta_MellinPrinciple
import Definitions.Def_DedekindZeta_GammaIntegral
import Definitions.Def_DedekindZeta_ConeRadialReduction
import Theorems.Thm_DedekindZeta_ConeRadialReduction_mem_normEqOneSurface
import Theorems.Thm_DedekindZeta_ConeRadialReduction_norm_radialMap
import Theorems.Thm_DedekindZeta_ConeRadialReduction_radialMap_mem_cone
import Theorems.Thm_DedekindZeta_ConeRadialReduction_radialMap_radialMap
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
    (DedekindZeta.mixedMulHaar K)
        (mixedEmbedding.fundamentalCone K ∩
          {x | mixedEmbedding.norm x ∈ Set.Ioc 1 (Real.exp 1)}) < ⊤ := by
  classical
  set C : Set (mixedSpace K) := mixedEmbedding.fundamentalCone K ∩
      {x | mixedEmbedding.norm x ∈ Set.Ioc 1 (Real.exp 1)} with hCdef
  have hCmeas : MeasurableSet C := by
    refine (measurableSet_fundamentalCone K).inter ?_
    exact (mixedEmbedding.continuous_norm K).measurable measurableSet_Ioc
  have hdensity : (DedekindZeta.mixedMulHaar K) C
      = ∫⁻ x in C, ENNReal.ofReal
          ((2 / Real.pi) ^ nrComplexPlaces K * (mixedEmbedding.norm x)⁻¹) ∂volume :=
    withDensity_apply _ hCmeas
  have hbound : (DedekindZeta.mixedMulHaar K) C
      ≤ ENNReal.ofReal ((2 / Real.pi) ^ nrComplexPlaces K) * volume C := by
    rw [hdensity, ← setLIntegral_const C]
    refine setLIntegral_mono measurable_const ?_
    rintro x ⟨-, hxN⟩
    apply ENNReal.ofReal_le_ofReal
    have hxpos : 0 < mixedEmbedding.norm x := lt_trans one_pos hxN.1
    have hinv : (mixedEmbedding.norm x)⁻¹ ≤ 1 := (inv_le_one₀ hxpos).mpr hxN.1.le
    calc (2 / Real.pi) ^ nrComplexPlaces K * (mixedEmbedding.norm x)⁻¹
        ≤ (2 / Real.pi) ^ nrComplexPlaces K * 1 :=
          mul_le_mul_of_nonneg_left hinv (by positivity)
      _ = (2 / Real.pi) ^ nrComplexPlaces K := mul_one _
  refine lt_of_le_of_lt hbound (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_)
  have hepos : 0 < Real.exp 1 := Real.exp_pos 1
  have hCbdd : Bornology.IsBounded C := by
    refine ((fundamentalCone.isBounded_normLeOne K).smul₀
      ((Real.exp 1) ^ ((finrank ℚ K : ℝ)⁻¹))).subset ?_
    rintro x ⟨hxcone, hxN⟩
    refine Set.mem_smul_set.mpr ⟨radialMap K (Real.exp 1)⁻¹ x, ?_, ?_⟩
    · rw [fundamentalCone.mem_normLeOne]
      refine ⟨radialMap_mem_cone (Real.exp 1)⁻¹ (inv_pos.mpr hepos) hxcone, ?_⟩
      rw [norm_radialMap (Real.exp 1)⁻¹ (inv_pos.mpr hepos) x]
      calc (Real.exp 1)⁻¹ * mixedEmbedding.norm x
          ≤ (Real.exp 1)⁻¹ * Real.exp 1 :=
            mul_le_mul_of_nonneg_left hxN.2 (inv_pos.mpr hepos).le
        _ = 1 := inv_mul_cancel₀ hepos.ne'
    · show radialMap K (Real.exp 1) (radialMap K (Real.exp 1)⁻¹ x) = x
      rw [radialMap_radialMap (Real.exp 1) (Real.exp 1)⁻¹ hepos.le (inv_pos.mpr hepos).le,
        mul_inv_cancel₀ hepos.ne']
      simp [radialMap]
  exact hCbdd.measure_lt_top
end DedekindZeta.ConeRadialReduction
