-- Prove2me | solution 1 for DedekindZeta.ConeRadialReduction.orbitTheta_inv_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:52:34.84324+00:00
-- url     : https://prove2.me/submissions/c5b2a023-0bbe-4553-a444-017fac79d712

import Mathlib
import Definitions.Def_DedekindZeta_Statements
import Definitions.Def_DedekindZeta_MellinPrinciple
import Definitions.Def_DedekindZeta_GammaIntegral
import Definitions.Def_DedekindZeta_ConeRadialReduction
import Theorems.Thm_DedekindZeta_ConeRadialReduction_mem_normEqOneSurface
import Theorems.Thm_DedekindZeta_ConeRadialReduction_measurableSet_normEqOneSurface
import Theorems.Thm_DedekindZeta_ConeRadialReduction_norm_radialMap
import Theorems.Thm_DedekindZeta_ConeRadialReduction_radialMap_mem_cone
import Theorems.Thm_DedekindZeta_ConeRadialReduction_surfaceMeasure_apply_compl_normEqOneSurface
import Theorems.Thm_DedekindZeta_ConeRadialReduction_continuousOn_mixedThetaKernel_radialMap
import Theorems.Thm_DedekindZeta_ConeRadialReduction_exists_bound_mixedThetaKernel_radialMap
import Theorems.Thm_DedekindZeta_ConeRadialReduction_radialMap_inv
import Theorems.Thm_DedekindZeta_ConeRadialReduction_continuousOn_inv_norm_ne_zero
import Theorems.Thm_DedekindZeta_ConeRadialReduction_mixedMulHaar_collar_lt_top
import Theorems.Thm_DedekindZeta_ConeRadialReduction_integral_surface_inv
import Theorems.Thm_DedekindZeta_Theta_continuousOn_idealThetaKernel
import Theorems.Thm_DedekindZeta_Theta_gaussVSchwartz_apply
import Theorems.Thm_DedekindZeta_Theta_idealThetaKernel_eq_mixed
import Theorems.Thm_DedekindZeta_Theta_idealThetaKernel_unitSMul
import Theorems.Thm_DedekindZeta_Theta_mixedGaussianSchwartz_apply
import Theorems.Thm_DedekindZeta_ae_norm_ne_zero
import Theorems.Thm_DedekindZeta_mixedEmbedding_norm_inv
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
theorem _root_.solution (𝔞 : Ideal (𝓞 K)) (r : ℝ) (hr : 0 < r) :
    orbitTheta K 𝔞 (1 / r)
      = ∫ σ in normEqOneSurface K,
          Theta.idealThetaKernel K 𝔞 (radialMap K r σ)⁻¹ ∂(surfaceMeasure K) := by
  classical
  have hr1 : (0 : ℝ) < 1 / r := div_pos one_pos hr
  set f : mixedSpace K → ℂ :=
    fun σ => Theta.idealThetaKernel K 𝔞 (radialMap K (1 / r) σ) with hf_def
  set C : Set (mixedSpace K) := mixedEmbedding.fundamentalCone K ∩
      {x | mixedEmbedding.norm x ∈ Set.Ioc 1 (Real.exp 1)} with hCdef
  have hCmeas : MeasurableSet C :=
    (measurableSet_fundamentalCone K).inter
      ((mixedEmbedding.continuous_norm K).measurable measurableSet_Ioc)
  have hq : (0 : ℝ) ≤ ((finrank ℚ K : ℝ))⁻¹ := by positivity
  -- Measurable set `{N ≠ 0}` and `surfaceMeasure` support fact.
  have hms : MeasurableSet {x : mixedSpace K | mixedEmbedding.norm x ≠ 0} := by
    have heq : {x : mixedSpace K | mixedEmbedding.norm x ≠ 0}
        = {x | mixedEmbedding.norm x = 0}ᶜ := by ext x; simp
    rw [heq]
    exact (measurableSet_eq_fun (mixedEmbedding.continuous_norm K).measurable
      measurable_const).compl
  have hae : ∀ᵐ σ ∂(surfaceMeasure K), σ ∈ normEqOneSurface K := by
    rw [ae_iff]
    simpa only [Set.mem_compl_iff, Set.compl_def] using
      surfaceMeasure_apply_compl_normEqOneSurface
  have hSsub : normEqOneSurface K ⊆ {x : mixedSpace K | mixedEmbedding.norm x ≠ 0} :=
    fun σ hσ => by
      simp only [Set.mem_setOf_eq, (mem_normEqOneSurface.mp hσ).2]; exact one_ne_zero
  -- Unit-invariance of `f`.
  have hunit : ∀ (u : (𝓞 K)ˣ) (x : mixedSpace K), f (u • x) = f x := by
    intro u x
    simp only [hf_def]
    have hcomm : radialMap K (1 / r) (u • x) = u • radialMap K (1 / r) x := by
      simp only [radialMap, NumberField.mixedEmbedding.unitSMul_smul]
      exact (Algebra.mul_smul_comm _ _ _).symm
    simp only [hcomm, Theta.idealThetaKernel_unitSMul]
  -- Continuity of `f` and `f ∘ inv` on the norm-1 surface.
  have hfcont : ContinuousOn f (normEqOneSurface K) := by
    have h := (continuousOn_mixedThetaKernel_radialMap K
      (𝔞 : FractionalIdeal (𝓞 K)⁰ K) (1 / r) hr1).mono subset_closure
    simpa only [hf_def, ← Theta.idealThetaKernel_eq_mixed] using h
  have hf_meas : AEStronglyMeasurable f (surfaceMeasure K) := by
    rw [← Measure.restrict_eq_self_of_ae_mem hae]
    exact hfcont.aestronglyMeasurable measurableSet_normEqOneSurface
  have hfinvcont : ContinuousOn (fun σ => f σ⁻¹) (normEqOneSurface K) := by
    have hinv : ContinuousOn (Inv.inv : mixedSpace K → mixedSpace K)
        (normEqOneSurface K) := (continuousOn_inv_norm_ne_zero K).mono hSsub
    have hrm : ContinuousOn (fun σ => radialMap K (1 / r) σ⁻¹) (normEqOneSurface K) :=
      ((continuous_const_smul ((1 / r) ^ ((finrank ℚ K : ℝ)⁻¹))).continuousOn).comp
        hinv (Set.mapsTo_univ _ _)
    have hmaps : Set.MapsTo (fun σ => radialMap K (1 / r) σ⁻¹) (normEqOneSurface K)
        {x : mixedSpace K | mixedEmbedding.norm x ≠ 0} := by
      intro σ hσ
      have hN : mixedEmbedding.norm (radialMap K (1 / r) σ⁻¹) = 1 / r := by
        rw [norm_radialMap (1 / r) hr1, DedekindZeta.mixedEmbedding_norm_inv,
          (mem_normEqOneSurface.mp hσ).2, inv_one, mul_one]
      simp only [Set.mem_setOf_eq, hN]; exact hr1.ne'
    have := (Theta.continuousOn_idealThetaKernel K 𝔞).comp hrm hmaps
    simpa only [hf_def, Function.comp_def] using this
  have hfinv_meas : AEStronglyMeasurable (fun σ => f σ⁻¹) (surfaceMeasure K) := by
    rw [← Measure.restrict_eq_self_of_ae_mem hae]
    exact hfinvcont.aestronglyMeasurable measurableSet_normEqOneSurface
  -- Continuity of `f ∘ radialProj` on the nonzero-norm locus.
  have hscalarcont : ContinuousOn
      (fun x : mixedSpace K => (mixedEmbedding.norm x)⁻¹ ^ ((finrank ℚ K : ℝ)⁻¹))
      {x : mixedSpace K | mixedEmbedding.norm x ≠ 0} :=
    (Real.continuous_rpow_const hq).comp_continuousOn
      ((mixedEmbedding.continuous_norm K).continuousOn.inv₀ (fun x hx => hx))
  have hprojcont : ContinuousOn (radialProj K)
      {x : mixedSpace K | mixedEmbedding.norm x ≠ 0} :=
    hscalarcont.smul continuousOn_id
  have hg1 : ContinuousOn (fun x => radialMap K (1 / r) (radialProj K x))
      {x : mixedSpace K | mixedEmbedding.norm x ≠ 0} :=
    ((continuous_const_smul ((1 / r) ^ ((finrank ℚ K : ℝ)⁻¹))).continuousOn).comp
      hprojcont (Set.mapsTo_univ _ _)
  have hg2 : Set.MapsTo (fun x => radialMap K (1 / r) (radialProj K x))
      {x : mixedSpace K | mixedEmbedding.norm x ≠ 0}
      {x : mixedSpace K | mixedEmbedding.norm x ≠ 0} := by
    intro x hx
    have hpos : 0 < mixedEmbedding.norm x :=
      (mixedEmbedding.norm_nonneg x).lt_of_ne (Ne.symm hx)
    have hN1 : mixedEmbedding.norm (radialProj K x) = 1 := by
      rw [radialProj, norm_radialMap _ (inv_pos.mpr hpos), inv_mul_cancel₀ hpos.ne']
    simp only [Set.mem_setOf_eq, norm_radialMap (1 / r) hr1, hN1, mul_one]
    exact hr1.ne'
  have hgcont : ContinuousOn (fun x => f (radialProj K x))
      {x : mixedSpace K | mixedEmbedding.norm x ≠ 0} := by
    have := (Theta.continuousOn_idealThetaKernel K 𝔞).comp hg1 hg2
    simpa only [hf_def, Function.comp_def] using this
  have hg_meas : AEStronglyMeasurable (fun x => f (radialProj K x))
      (DedekindZeta.mixedMulHaar K) := by
    rw [← Measure.restrict_eq_self_of_ae_mem DedekindZeta.ae_norm_ne_zero]
    exact hgcont.aestronglyMeasurable hms
  -- Integrability of `f ∘ radialProj` on the finite-measure collar.
  have hg_int : IntegrableOn (fun x => f (radialProj K x)) C
      (DedekindZeta.mixedMulHaar K) := by
    obtain ⟨M, hM⟩ := exists_bound_mixedThetaKernel_radialMap K
      (𝔞 : FractionalIdeal (𝓞 K)⁰ K) (1 / r) hr1
    haveI : IsFiniteMeasure ((DedekindZeta.mixedMulHaar K).restrict C) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact mixedMulHaar_collar_lt_top⟩
    refine Integrable.mono' (integrable_const M) hg_meas.restrict ?_
    refine (ae_restrict_iff' hCmeas).mpr (Filter.Eventually.of_forall (fun x hx => ?_))
    obtain ⟨hxc, hxN⟩ := hx
    simp only [Set.mem_setOf_eq, Set.mem_Ioc] at hxN
    have hpos : 0 < mixedEmbedding.norm x := lt_trans one_pos hxN.1
    have hσ : radialProj K x ∈ normEqOneSurface K := by
      refine mem_normEqOneSurface.mpr ⟨radialMap_mem_cone _ (inv_pos.mpr hpos) hxc, ?_⟩
      rw [radialProj, norm_radialMap _ (inv_pos.mpr hpos), inv_mul_cancel₀ hpos.ne']
    change ‖f (radialProj K x)‖ ≤ M
    rw [hf_def]
    simp only [Theta.idealThetaKernel_eq_mixed]
    exact hM (radialProj K x) hσ
  rw [orbitTheta, ← hf_def]
  have hsub : (∫ σ in normEqOneSurface K, f σ ∂(surfaceMeasure K))
        = ∫ σ in normEqOneSurface K, f σ⁻¹ ∂(surfaceMeasure K) :=
    (integral_surface_inv K f hunit hf_meas hfinv_meas hg_meas hg_int).symm
  rw [hsub]
  refine setIntegral_congr_fun measurableSet_normEqOneSurface (fun σ _ => ?_)
  simp only [hf_def, radialMap_inv r hr σ]
end DedekindZeta.ConeRadialReduction
