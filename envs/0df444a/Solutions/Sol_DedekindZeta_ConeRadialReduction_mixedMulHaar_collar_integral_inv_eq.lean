-- Prove2me | solution 1 for DedekindZeta.ConeRadialReduction.mixedMulHaar_collar_integral_inv_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:48:38.486612+00:00
-- url     : https://prove2.me/submissions/ce778afa-73dd-4334-8f0c-2025d6d70995

import Mathlib
import Definitions.Def_DedekindZeta_Statements
import Definitions.Def_DedekindZeta_MellinPrinciple
import Definitions.Def_DedekindZeta_GammaIntegral
import Definitions.Def_DedekindZeta_ConeRadialReduction
import Theorems.Thm_DedekindZeta_ConeRadialReduction_mem_normEqOneSurface
import Theorems.Thm_DedekindZeta_ConeRadialReduction_radialMap_mem_cone
import Theorems.Thm_DedekindZeta_ConeRadialReduction_radialMap_radialMap
import Theorems.Thm_DedekindZeta_ConeRadialReduction_radialMap_inv
import Theorems.Thm_DedekindZeta_ConeRadialReduction_setIntegral_reflected_collar_eq
import Theorems.Thm_DedekindZeta_Theta_gaussVSchwartz_apply
import Theorems.Thm_DedekindZeta_Theta_mixedGaussianSchwartz_apply
import Theorems.Thm_DedekindZeta_Theta_norm_unitSMul
import Theorems.Thm_DedekindZeta_measurable_mixedSpace_inv
import Theorems.Thm_DedekindZeta_mixedEmbedding_norm_inv
import Theorems.Thm_DedekindZeta_mixedMulHaar_integral_inv_cone_eq
import Theorems.Thm_DedekindZeta_mulHaar_integral_comp_inv
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
theorem _root_.solution (g : mixedSpace K → ℂ)
    (hunit : ∀ (u : (𝓞 K)ˣ) (x : mixedSpace K), g (u • x) = g x)
    (hscale : ∀ (t : ℝ), 0 < t → ∀ x, g (radialMap K t x) = g x)
    (hmeas : AEStronglyMeasurable g (DedekindZeta.mixedMulHaar K))
    (hint : IntegrableOn g
      (mixedEmbedding.fundamentalCone K ∩
        {x | mixedEmbedding.norm x ∈ Set.Ioc 1 (Real.exp 1)})
      (DedekindZeta.mixedMulHaar K)) :
    ∫ x in (mixedEmbedding.fundamentalCone K ∩
          {x | mixedEmbedding.norm x ∈ Set.Ioc 1 (Real.exp 1)}),
        g x⁻¹ ∂(DedekindZeta.mixedMulHaar K)
      = ∫ x in (mixedEmbedding.fundamentalCone K ∩
          {x | mixedEmbedding.norm x ∈ Set.Ioc 1 (Real.exp 1)}),
        g x ∂(DedekindZeta.mixedMulHaar K) := by
  classical
  have he : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have hA_meas : MeasurableSet
      {x : mixedSpace K | mixedEmbedding.norm x ∈ Set.Ioc 1 (Real.exp 1)} :=
    (mixedEmbedding.continuous_norm K).measurable measurableSet_Ioc
  have hcone_meas : MeasurableSet (mixedEmbedding.fundamentalCone K) :=
    measurableSet_fundamentalCone K
  have hC_meas : MeasurableSet (mixedEmbedding.fundamentalCone K ∩
      {x | mixedEmbedding.norm x ∈ Set.Ioc 1 (Real.exp 1)}) := hcone_meas.inter hA_meas
  -- inversion image = preimage (involutive), hence measurable
  have himg_eq : ∀ T : Set (mixedSpace K),
      (fun y : mixedSpace K => y⁻¹) '' T = (fun y => y⁻¹) ⁻¹' T := by
    intro T; ext z
    simp only [Set.mem_image, Set.mem_preimage]
    constructor
    · rintro ⟨y, hy, rfl⟩; rwa [inv_inv]
    · intro hz; exact ⟨z⁻¹, hz, inv_inv z⟩
  have hinvcone_meas : MeasurableSet
      ((fun y : mixedSpace K => y⁻¹) '' mixedEmbedding.fundamentalCone K) := by
    rw [himg_eq]; exact DedekindZeta.measurable_mixedSpace_inv hcone_meas
  have hinvC_meas : MeasurableSet ((fun y : mixedSpace K => y⁻¹) ''
      (mixedEmbedding.fundamentalCone K ∩
        {x | mixedEmbedding.norm x ∈ Set.Ioc 1 (Real.exp 1)})) := by
    rw [himg_eq]; exact DedekindZeta.measurable_mixedSpace_inv hC_meas
  -- `radialMap K 1 = id`
  have hone : ∀ z : mixedSpace K, radialMap K 1 z = z := fun z => by
    simp [radialMap, Real.one_rpow, one_smul]
  -- the inverse cone is scale-invariant
  have hSinv : ∀ (t : ℝ), 0 < t → ∀ x,
      (radialMap K t x ∈ (fun y : mixedSpace K => y⁻¹) '' mixedEmbedding.fundamentalCone K
        ↔ x ∈ (fun y : mixedSpace K => y⁻¹) '' mixedEmbedding.fundamentalCone K) := by
    intro t ht x
    simp only [himg_eq, Set.mem_preimage]
    have hkey : (radialMap K t x)⁻¹ = radialMap K t⁻¹ x⁻¹ := by
      have h := radialMap_inv t ht x; rw [one_div] at h; exact h.symm
    rw [hkey]
    constructor
    · intro h
      have h2 := radialMap_mem_cone t ht h
      rwa [radialMap_radialMap t t⁻¹ ht.le (inv_pos.mpr ht).le,
        mul_inv_cancel₀ ht.ne', hone] at h2
    · intro h; exact radialMap_mem_cone t⁻¹ (inv_pos.mpr ht) h
  -- collar reflection bijection: `N x⁻¹ = (N x)⁻¹` flips `(1, e]` to `[1/e, 1)`
  have hball2 : ∀ z : ℝ, 0 ≤ z →
      (z ∈ Set.Ioc 1 (Real.exp 1) ↔ z⁻¹ ∈ Set.Ico (Real.exp 1)⁻¹ 1) := by
    intro z hz0
    rcases eq_or_lt_of_le hz0 with h | hz
    · subst h
      simp only [Set.mem_Ioc, Set.mem_Ico, inv_zero]
      constructor
      · rintro ⟨h1, _⟩; exact absurd h1 (by norm_num)
      · rintro ⟨h1, _⟩; exact absurd h1 (not_le.mpr (inv_pos.mpr he))
    · simp only [Set.mem_Ioc, Set.mem_Ico]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨(inv_le_inv₀ he hz).mpr h2, inv_lt_one_of_one_lt₀ h1⟩
      · rintro ⟨h1, h2⟩
        exact ⟨(inv_lt_one₀ hz).mp h2, (inv_le_inv₀ he hz).mp h1⟩
  have claim1 : (fun y : mixedSpace K => y⁻¹) ''
      (mixedEmbedding.fundamentalCone K ∩
        {x | mixedEmbedding.norm x ∈ Set.Ioc 1 (Real.exp 1)})
      = ((fun y : mixedSpace K => y⁻¹) '' mixedEmbedding.fundamentalCone K)
        ∩ {x | mixedEmbedding.norm x ∈ Set.Ico (Real.exp 1)⁻¹ 1} := by
    ext z
    simp only [Set.mem_image, Set.mem_inter_iff, Set.mem_setOf_eq]
    constructor
    · rintro ⟨y, ⟨hyc, hyA⟩, rfl⟩
      refine ⟨⟨y, hyc, rfl⟩, ?_⟩
      rw [DedekindZeta.mixedEmbedding_norm_inv (K := K) y]
      exact (hball2 (mixedEmbedding.norm y) (mixedEmbedding.norm_nonneg y)).mp hyA
    · rintro ⟨⟨y, hyc, rfl⟩, hz⟩
      refine ⟨y, ⟨hyc, ?_⟩, rfl⟩
      rw [DedekindZeta.mixedEmbedding_norm_inv (K := K) y] at hz
      exact (hball2 (mixedEmbedding.norm y) (mixedEmbedding.norm_nonneg y)).mpr hz
  calc
    ∫ x in (mixedEmbedding.fundamentalCone K ∩
          {x | mixedEmbedding.norm x ∈ Set.Ioc 1 (Real.exp 1)}),
        g x⁻¹ ∂(DedekindZeta.mixedMulHaar K)
        = ∫ x in ((fun y : mixedSpace K => y⁻¹) ''
            (mixedEmbedding.fundamentalCone K ∩
              {x | mixedEmbedding.norm x ∈ Set.Ioc 1 (Real.exp 1)})),
            g x ∂(DedekindZeta.mixedMulHaar K) := by
          -- (A) inversion change of variables
          rw [← integral_indicator hC_meas, ← integral_indicator hinvC_meas]
          have hpt : (fun x => (mixedEmbedding.fundamentalCone K ∩
                {x | mixedEmbedding.norm x ∈ Set.Ioc 1 (Real.exp 1)}).indicator
                  (fun y => g y⁻¹) x)
              = fun x => ((fun y : mixedSpace K => y⁻¹) ''
                  (mixedEmbedding.fundamentalCone K ∩
                    {x | mixedEmbedding.norm x ∈ Set.Ioc 1 (Real.exp 1)})).indicator g x⁻¹ := by
            funext x
            by_cases hx : x ∈ (mixedEmbedding.fundamentalCone K ∩
                {x | mixedEmbedding.norm x ∈ Set.Ioc 1 (Real.exp 1)})
            · rw [Set.indicator_of_mem hx,
                Set.indicator_of_mem (Set.mem_image_of_mem _ hx)]
            · have hxinv : x⁻¹ ∉ ((fun y : mixedSpace K => y⁻¹) ''
                  (mixedEmbedding.fundamentalCone K ∩
                    {x | mixedEmbedding.norm x ∈ Set.Ioc 1 (Real.exp 1)})) := by
                rintro ⟨y, hy, hyx⟩
                have hyx2 : y⁻¹ = x⁻¹ := hyx
                have hyx' : y = x := by rw [← inv_inv y, hyx2, inv_inv]
                exact hx (hyx' ▸ hy)
              rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hxinv]
          rw [hpt]
          exact (DedekindZeta.mulHaar_integral_comp_inv
            (fun x => ((fun y : mixedSpace K => y⁻¹) ''
              (mixedEmbedding.fundamentalCone K ∩
                {x | mixedEmbedding.norm x ∈ Set.Ioc 1 (Real.exp 1)})).indicator g x)
            (hmeas.indicator hinvC_meas)).symm
    _ = ∫ x in (((fun y : mixedSpace K => y⁻¹) '' mixedEmbedding.fundamentalCone K)
          ∩ {x | mixedEmbedding.norm x ∈ Set.Ico (Real.exp 1)⁻¹ 1}),
            g x ∂(DedekindZeta.mixedMulHaar K) := by rw [claim1]
    _ = ∫ x in (((fun y : mixedSpace K => y⁻¹) '' mixedEmbedding.fundamentalCone K)
          ∩ {x | mixedEmbedding.norm x ∈ Set.Ioc 1 (Real.exp 1)}),
            g x ∂(DedekindZeta.mixedMulHaar K) :=
          -- (B) collar reflection on the inverse cone
          setIntegral_reflected_collar_eq hinvcone_meas hSinv g hmeas hscale
    _ = ∫ x in (mixedEmbedding.fundamentalCone K ∩
          {x | mixedEmbedding.norm x ∈ Set.Ioc 1 (Real.exp 1)}),
            g x ∂(DedekindZeta.mixedMulHaar K) := by
          -- (C) unit-fundamental-domain inversion
          have hAg_unit : ∀ (u : (𝓞 K)ˣ) (x : mixedSpace K),
              ({x | mixedEmbedding.norm x ∈ Set.Ioc 1 (Real.exp 1)}).indicator g (u • x)
                = ({x | mixedEmbedding.norm x ∈ Set.Ioc 1 (Real.exp 1)}).indicator g x := by
            intro u x
            simp only [Set.indicator_apply, Set.mem_setOf_eq, Theta.norm_unitSMul, hunit]
          have hAg_int : Integrable
              ((mixedEmbedding.fundamentalCone K).indicator
                (({x | mixedEmbedding.norm x ∈ Set.Ioc 1 (Real.exp 1)}).indicator g))
              (DedekindZeta.mixedMulHaar K) := by
            rw [Set.indicator_indicator]
            exact (integrable_indicator_iff hC_meas).mpr hint
          have hstepC := DedekindZeta.mixedMulHaar_integral_inv_cone_eq
            (({x | mixedEmbedding.norm x ∈ Set.Ioc 1 (Real.exp 1)}).indicator g)
            hAg_unit (hmeas.indicator hA_meas) hAg_int
          rw [Set.indicator_indicator, Set.indicator_indicator,
            integral_indicator (hinvcone_meas.inter hA_meas),
            integral_indicator hC_meas] at hstepC
          exact hstepC
end DedekindZeta.ConeRadialReduction
