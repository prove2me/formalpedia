-- Prove2me | solution 1 for DedekindZeta.ConeRadialReduction.setIntegral_reflected_collar_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:47:08.702239+00:00
-- url     : https://prove2.me/submissions/eb0af79d-31cf-4ee5-ba3b-ebcdaf836439

import Mathlib
import Definitions.Def_DedekindZeta_Statements
import Definitions.Def_DedekindZeta_MellinPrinciple
import Definitions.Def_DedekindZeta_GammaIntegral
import Definitions.Def_DedekindZeta_ConeRadialReduction
import Theorems.Thm_DedekindZeta_ConeRadialReduction_mem_normEqOneSurface
import Theorems.Thm_DedekindZeta_ConeRadialReduction_mixedMulHaar_norm_eq_eq_zero
import Theorems.Thm_DedekindZeta_ConeRadialReduction_setIntegral_collar_shift
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
theorem _root_.solution {S : Set (mixedSpace K)} (hS : MeasurableSet S)
    (hSinv : ∀ (t : ℝ), 0 < t → ∀ x, (radialMap K t x ∈ S ↔ x ∈ S))
    (g : mixedSpace K → ℂ)
    (hg : AEStronglyMeasurable g (DedekindZeta.mixedMulHaar K))
    (hgscale : ∀ (t : ℝ), 0 < t → ∀ x, g (radialMap K t x) = g x) :
    ∫ x in (S ∩ {x | mixedEmbedding.norm x ∈ Set.Ico (Real.exp 1)⁻¹ 1}),
        g x ∂(DedekindZeta.mixedMulHaar K)
      = ∫ x in (S ∩ {x | mixedEmbedding.norm x ∈ Set.Ioc 1 (Real.exp 1)}),
          g x ∂(DedekindZeta.mixedMulHaar K) := by
  classical
  have hepos : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  set a : ℝ := (Real.exp 1)⁻¹ with ha
  have hapos : 0 < a := inv_pos.mpr hepos
  have hmul : Real.exp 1 * a = 1 := by rw [ha, mul_inv_cancel₀ hepos.ne']
  have hshift := setIntegral_collar_shift hS hSinv g hg hgscale (t := a) hapos
  rw [hmul] at hshift
  have haeeq : {x : mixedSpace K | mixedEmbedding.norm x ∈ Set.Ico a 1}
      =ᵐ[DedekindZeta.mixedMulHaar K] {x | mixedEmbedding.norm x ∈ Set.Ioc a 1} := by
    refine MeasureTheory.ae_eq_set.mpr ⟨?_, ?_⟩
    · refine measure_mono_null (t := {x : mixedSpace K | mixedEmbedding.norm x = a}) ?_
        (mixedMulHaar_norm_eq_eq_zero hapos)
      intro x hx
      obtain ⟨hin, hout⟩ := hx
      simp only [Set.mem_setOf_eq, Set.mem_Ico] at hin
      simp only [Set.mem_setOf_eq, Set.mem_Ioc, not_and, not_le] at hout
      rcases eq_or_lt_of_le hin.1 with h | h
      · exact h.symm
      · exact absurd (hout h) (not_lt.mpr hin.2.le)
    · refine measure_mono_null (t := {x : mixedSpace K | mixedEmbedding.norm x = 1}) ?_
        (mixedMulHaar_norm_eq_eq_zero one_pos)
      intro x hx
      obtain ⟨hin, hout⟩ := hx
      simp only [Set.mem_setOf_eq, Set.mem_Ioc] at hin
      simp only [Set.mem_setOf_eq, Set.mem_Ico, not_and, not_lt] at hout
      rcases eq_or_lt_of_le hin.2 with h | h
      · exact h
      · exact absurd (hout hin.1.le) (not_le.mpr h)
  have hsetaeeq : (S ∩ {x : mixedSpace K | mixedEmbedding.norm x ∈ Set.Ico a 1}
        : Set (mixedSpace K))
      =ᵐ[DedekindZeta.mixedMulHaar K]
        (S ∩ {x | mixedEmbedding.norm x ∈ Set.Ioc a 1} : Set (mixedSpace K)) := by
    refine MeasureTheory.ae_eq_set.mpr ⟨?_, ?_⟩
    · have hsub : (S ∩ {x : mixedSpace K | mixedEmbedding.norm x ∈ Set.Ico a 1})
          \ (S ∩ {x | mixedEmbedding.norm x ∈ Set.Ioc a 1})
          ⊆ {x : mixedSpace K | mixedEmbedding.norm x ∈ Set.Ico a 1}
            \ {x | mixedEmbedding.norm x ∈ Set.Ioc a 1} :=
        fun x hx => ⟨hx.1.2, fun hB => hx.2 ⟨hx.1.1, hB⟩⟩
      exact measure_mono_null hsub (MeasureTheory.ae_eq_set.mp haeeq).1
    · have hsub : (S ∩ {x : mixedSpace K | mixedEmbedding.norm x ∈ Set.Ioc a 1})
          \ (S ∩ {x | mixedEmbedding.norm x ∈ Set.Ico a 1})
          ⊆ {x : mixedSpace K | mixedEmbedding.norm x ∈ Set.Ioc a 1}
            \ {x | mixedEmbedding.norm x ∈ Set.Ico a 1} :=
        fun x hx => ⟨hx.1.2, fun hA => hx.2 ⟨hx.1.1, hA⟩⟩
      exact measure_mono_null hsub (MeasureTheory.ae_eq_set.mp haeeq).2
  rw [setIntegral_congr_set hsetaeeq, hshift]
end DedekindZeta.ConeRadialReduction
