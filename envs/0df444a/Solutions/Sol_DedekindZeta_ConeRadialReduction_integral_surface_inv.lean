-- Prove2me | solution 1 for DedekindZeta.ConeRadialReduction.integral_surface_inv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:50:20.760729+00:00
-- url     : https://prove2.me/submissions/de14bb5b-c947-40c4-8f78-66a237e247a9

import Mathlib
import Definitions.Def_DedekindZeta_Statements
import Definitions.Def_DedekindZeta_MellinPrinciple
import Definitions.Def_DedekindZeta_GammaIntegral
import Definitions.Def_DedekindZeta_ConeRadialReduction
import Theorems.Thm_DedekindZeta_ConeRadialReduction_mem_normEqOneSurface
import Theorems.Thm_DedekindZeta_ConeRadialReduction_surfaceMeasure_apply_compl_normEqOneSurface
import Theorems.Thm_DedekindZeta_ConeRadialReduction_radialProj_inv
import Theorems.Thm_DedekindZeta_ConeRadialReduction_radialProj_unitSMul
import Theorems.Thm_DedekindZeta_ConeRadialReduction_radialProj_radialMap
import Theorems.Thm_DedekindZeta_ConeRadialReduction_mixedMulHaar_collar_integral_inv_eq
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
theorem _root_.solution (f : mixedSpace K → ℂ)
    (hf : ∀ (u : (𝓞 K)ˣ) (x : mixedSpace K), f (u • x) = f x)
    (hf_meas : AEStronglyMeasurable f (surfaceMeasure K))
    (hfinv_meas : AEStronglyMeasurable (fun σ => f σ⁻¹) (surfaceMeasure K))
    (hg_meas : AEStronglyMeasurable (fun x => f (radialProj K x))
      (DedekindZeta.mixedMulHaar K))
    (hg_int : IntegrableOn (fun x => f (radialProj K x))
      (mixedEmbedding.fundamentalCone K ∩
        {x | mixedEmbedding.norm x ∈ Set.Ioc 1 (Real.exp 1)})
      (DedekindZeta.mixedMulHaar K)) :
    ∫ σ in normEqOneSurface K, f σ⁻¹ ∂(surfaceMeasure K)
      = ∫ σ in normEqOneSurface K, f σ ∂(surfaceMeasure K) := by
  classical
  -- The four side conditions are pure measurability/integrability hypotheses
  -- (not a mathematical strengthening); they are discharged at the consumer
  -- `orbitTheta_inv_apply` from continuity of the theta kernel on the
  -- nonzero-norm locus and finiteness of the norm collar.
  set C : Set (mixedSpace K) := mixedEmbedding.fundamentalCone K ∩
      {x | mixedEmbedding.norm x ∈ Set.Ioc 1 (Real.exp 1)} with hCdef
  have hCmeas : MeasurableSet C :=
    (measurableSet_fundamentalCone K).inter
      ((mixedEmbedding.continuous_norm K).measurable measurableSet_Ioc)
  have hq : (0 : ℝ) ≤ ((finrank ℚ K : ℝ))⁻¹ := by positivity
  have hscalar : Measurable
      (fun x : mixedSpace K => (mixedEmbedding.norm x)⁻¹ ^ ((finrank ℚ K : ℝ))⁻¹) :=
    (Real.continuous_rpow_const hq).measurable.comp
      ((mixedEmbedding.continuous_norm K).measurable.inv)
  have hmeasproj : Measurable (radialProj K) := hscalar.smul measurable_id
  -- `surfaceMeasure K` is supported on the norm-1 surface.
  have hae : ∀ᵐ σ ∂(surfaceMeasure K), σ ∈ normEqOneSurface K := by
    rw [ae_iff]
    simpa only [Set.mem_compl_iff, Set.compl_def] using
      surfaceMeasure_apply_compl_normEqOneSurface
  -- Transport a surface integral to the norm collar via the `radialProj` pushforward.
  have key : ∀ F : mixedSpace K → ℂ, AEStronglyMeasurable F (surfaceMeasure K) →
      ∫ σ in normEqOneSurface K, F σ ∂(surfaceMeasure K)
        = ∫ x in C, F (radialProj K x) ∂(DedekindZeta.mixedMulHaar K) := by
    intro F hF
    rw [← integral_eq_setIntegral hae]
    exact integral_map hmeasproj.aemeasurable hF
  rw [key (fun σ => f σ⁻¹) hfinv_meas, key f hf_meas]
  -- On the collar `N x ≠ 0`, so `(radialProj K x)⁻¹ = radialProj K x⁻¹`.
  have hcongr : ∫ x in C, f ((radialProj K x)⁻¹) ∂(DedekindZeta.mixedMulHaar K)
      = ∫ x in C, f (radialProj K x⁻¹) ∂(DedekindZeta.mixedMulHaar K) := by
    refine setIntegral_congr_fun hCmeas (fun x hx => ?_)
    obtain ⟨-, hxN⟩ := hx
    simp only [Set.mem_setOf_eq, Set.mem_Ioc] at hxN
    have hxNe : mixedEmbedding.norm x ≠ 0 := (lt_trans one_pos hxN.1).ne'
    rw [radialProj_inv hxNe]
  rw [hcongr]
  -- The remaining identity over the collar is the crux lemma applied to
  -- `g := f ∘ radialProj`, which is unit- and radial-scale-invariant.
  exact mixedMulHaar_collar_integral_inv_eq K (fun x => f (radialProj K x))
    (fun u x => by
      change f (radialProj K (u • x)) = f (radialProj K x)
      rw [radialProj_unitSMul]; exact hf u (radialProj K x))
    (fun t ht x => by
      change f (radialProj K (radialMap K t x)) = f (radialProj K x)
      rw [radialProj_radialMap ht])
    hg_meas hg_int
end DedekindZeta.ConeRadialReduction
