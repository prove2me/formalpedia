-- Prove2me | solution 1 for DedekindZeta.ConeRadialReduction.setIntegral_collar_shift
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:44:56.158969+00:00
-- url     : https://prove2.me/submissions/4765d62c-dbea-46bb-a093-5d0c0f3f4e01

import Mathlib
import Definitions.Def_DedekindZeta_Statements
import Definitions.Def_DedekindZeta_MellinPrinciple
import Definitions.Def_DedekindZeta_GammaIntegral
import Definitions.Def_DedekindZeta_ConeRadialReduction
import Theorems.Thm_DedekindZeta_ConeRadialReduction_mem_normEqOneSurface
import Theorems.Thm_DedekindZeta_ConeRadialReduction_norm_radialMap
import Theorems.Thm_DedekindZeta_Theta_gaussVSchwartz_apply
import Theorems.Thm_DedekindZeta_Theta_mixedGaussianSchwartz_apply
import Theorems.Thm_DedekindZeta_measurable_mul_right_mixedSpace
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
    (hgscale : ∀ (t : ℝ), 0 < t → ∀ x, g (radialMap K t x) = g x)
    {t : ℝ} (ht : 0 < t) :
    ∫ x in (S ∩ {x | mixedEmbedding.norm x ∈ Set.Ioc t (Real.exp 1 * t)}),
        g x ∂(DedekindZeta.mixedMulHaar K)
      = ∫ x in (S ∩ {x | mixedEmbedding.norm x ∈ Set.Ioc 1 (Real.exp 1)}),
          g x ∂(DedekindZeta.mixedMulHaar K) := by
  classical
  set C : Set (mixedSpace K) := S ∩
      {x | mixedEmbedding.norm x ∈ Set.Ioc 1 (Real.exp 1)} with hC
  set Ct : Set (mixedSpace K) := S ∩
      {y | mixedEmbedding.norm y ∈ Set.Ioc t (Real.exp 1 * t)} with hCt
  have hC_meas : MeasurableSet C :=
    hS.inter ((mixedEmbedding.continuous_norm K).measurable measurableSet_Ioc)
  have hCt_meas : MeasurableSet Ct :=
    hS.inter ((mixedEmbedding.continuous_norm K).measurable measurableSet_Ioc)
  have hiff : ∀ x, radialMap K t x ∈ Ct ↔ x ∈ C := by
    intro x
    rw [hCt, hC]
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, norm_radialMap t ht x, Set.mem_Ioc]
    constructor
    · rintro ⟨hSmem, hlo, hhi⟩
      refine ⟨(hSinv t ht x).mp hSmem, ?_, ?_⟩
      · exact lt_of_mul_lt_mul_left (by rwa [mul_one]) ht.le
      · exact le_of_mul_le_mul_left (by rwa [mul_comm (Real.exp 1) t] at hhi) ht
    · rintro ⟨hSmem, hlo, hhi⟩
      refine ⟨(hSinv t ht x).mpr hSmem, ?_, ?_⟩
      · have := mul_lt_mul_of_pos_left hlo ht
        rwa [mul_one] at this
      · have := mul_le_mul_of_nonneg_left hhi ht.le
        rwa [mul_comm t (Real.exp 1)] at this
  -- `radialMap K t` is right translation by the nonzero-norm scalar `c = s • 1`,
  -- hence `mixedMulHaar`-measure-preserving.
  set s : ℝ := t ^ ((finrank ℚ K : ℝ)⁻¹) with hs
  have hspos : 0 < s := Real.rpow_pos_of_pos ht _
  set c : mixedSpace K := s • (1 : mixedSpace K) with hc
  have hcN : mixedEmbedding.norm c ≠ 0 := by
    rw [hc, mixedEmbedding.norm_smul, map_one, mul_one]
    exact pow_ne_zero _ (abs_ne_zero.mpr hspos.ne')
  have hrw : (fun x : mixedSpace K => radialMap K t x) = fun x => x * c := by
    funext x; rw [radialMap, hc, mul_smul_comm, mul_one]
  have hmp : MeasurePreserving (fun x : mixedSpace K => radialMap K t x)
      (DedekindZeta.mixedMulHaar K) (DedekindZeta.mixedMulHaar K) := by
    rw [hrw]
    exact ⟨DedekindZeta.measurable_mul_right_mixedSpace K c,
      DedekindZeta.mixedMulHaar_map_mul_right (K := K) hcN⟩
  rw [← integral_indicator hCt_meas, ← integral_indicator hC_meas]
  have hpt : (fun x => C.indicator g x)
      = fun x => (Ct.indicator g) (radialMap K t x) := by
    funext x
    by_cases hx : x ∈ C
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem ((hiff x).mpr hx), hgscale t ht x]
    · rw [Set.indicator_of_notMem hx,
        Set.indicator_of_notMem (fun hcc => hx ((hiff x).mp hcc))]
  have hmap : (∫ x, Ct.indicator g x ∂(DedekindZeta.mixedMulHaar K))
      = ∫ y, Ct.indicator g y ∂(Measure.map (fun x => radialMap K t x)
          (DedekindZeta.mixedMulHaar K)) := by rw [hmp.map_eq]
  rw [hpt, hmap,
    integral_map hmp.measurable.aemeasurable
      (by rw [hmp.map_eq]; exact hg.indicator hCt_meas)]
end DedekindZeta.ConeRadialReduction
