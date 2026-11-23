-- Prove2me | solution 1 for DedekindZeta.ConeRadialReduction.setIntegral_cone_eq_radial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:44:45.942577+00:00
-- url     : https://prove2.me/submissions/74cf61b9-cb11-4e33-a74e-cc245e9c5205

import Mathlib
import Definitions.Def_DedekindZeta_Statements
import Definitions.Def_DedekindZeta_MellinPrinciple
import Definitions.Def_DedekindZeta_GammaIntegral
import Definitions.Def_DedekindZeta_ConeRadialReduction
import Theorems.Thm_DedekindZeta_ConeRadialReduction_mem_normEqOneSurface
import Theorems.Thm_DedekindZeta_ConeRadialReduction_continuous_radialMap_uncurry
import Theorems.Thm_DedekindZeta_ConeRadialReduction_surfaceMeasure_apply_compl_normEqOneSurface
import Theorems.Thm_DedekindZeta_ConeRadialReduction_mixedMulHaar_restrict_cone_eq_map
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
theorem _root_.solution (h : mixedSpace K → ℂ)
    (hh : IntegrableOn h (mixedEmbedding.fundamentalCone K) (DedekindZeta.mixedMulHaar K)) :
    ∫ x in mixedEmbedding.fundamentalCone K, h x ∂(DedekindZeta.mixedMulHaar K)
      = ∫ r in Set.Ioi (0 : ℝ),
          (∫ σ in normEqOneSurface K, h (radialMap K r σ) ∂(surfaceMeasure K)) * (r : ℝ)⁻¹
            ∂volume := by
  -- Notation: `F` is the radial parametrisation, `νd` the weighted product.
  haveI : SFinite (DedekindZeta.mixedMulHaar K) := by
    unfold DedekindZeta.mixedMulHaar; infer_instance
  haveI : SFinite (surfaceMeasure K) := by
    unfold surfaceMeasure; infer_instance
  have hbridge := mixedMulHaar_restrict_cone_eq_map (K := K)
  set F : ℝ × mixedSpace K → mixedSpace K := fun p => radialMap K p.1 p.2 with hFdef
  have hFmeas : Measurable F := continuous_radialMap_uncurry.measurable
  have hdens : Measurable (fun p : ℝ × mixedSpace K => ENNReal.ofReal p.1⁻¹) :=
    ENNReal.measurable_ofReal.comp measurable_fst.inv
  have hdenslt : ∀ᵐ p ∂(((volume.restrict (Set.Ioi (0 : ℝ))).prod (surfaceMeasure K))),
      ENNReal.ofReal p.1⁻¹ < ⊤ := ae_of_all _ (fun _ => ENNReal.ofReal_lt_top)
  -- The surface measure is supported on `normEqOneSurface K`.
  have hae : ∀ᵐ σ ∂(surfaceMeasure K), σ ∈ normEqOneSurface K := by
    rw [ae_iff]
    simpa only [Set.mem_compl_iff, Set.compl_def] using
      surfaceMeasure_apply_compl_normEqOneSurface
  -- Transfer the cone integral through the pushforward bridge.
  have hh' : Integrable h ((DedekindZeta.mixedMulHaar K).restrict
      (mixedEmbedding.fundamentalCone K)) := hh
  rw [hbridge] at hh'
  -- LHS: `∫ x in cone, h = ∫ x, h ∂(restrict cone) = ∫ x, h ∂(map F νd)`.
  rw [show (∫ x in mixedEmbedding.fundamentalCone K, h x ∂(DedekindZeta.mixedMulHaar K))
        = ∫ x, h x ∂((DedekindZeta.mixedMulHaar K).restrict
            (mixedEmbedding.fundamentalCone K)) from rfl, hbridge,
    integral_map hFmeas.aemeasurable hh'.aestronglyMeasurable,
    integral_withDensity_eq_integral_toReal_smul hdens hdenslt]
  -- Integrability of the weighted integrand against the product measure.
  have hint : Integrable
      (fun p : ℝ × mixedSpace K => (ENNReal.ofReal p.1⁻¹).toReal • h (F p))
      ((volume.restrict (Set.Ioi (0 : ℝ))).prod (surfaceMeasure K)) := by
    refine (integrable_withDensity_iff_integrable_smul' hdens hdenslt
      (g := fun p => h (F p))).mp ?_
    exact (integrable_map_measure hh'.aestronglyMeasurable hFmeas.aemeasurable).mp hh'
  -- Fubini.
  rw [integral_prod _ hint]
  simp only [hFdef]
  -- Inner `σ`-integral: pull out `r⁻¹`, extend the surface integral to `S K`.
  refine setIntegral_congr_fun measurableSet_Ioi (fun r hr => ?_)
  have hr0 : (0 : ℝ) < r := hr
  have hpos : (0 : ℝ) ≤ r⁻¹ := le_of_lt (inv_pos.mpr hr0)
  rw [integral_smul, ENNReal.toReal_ofReal hpos, Complex.real_smul, mul_comm,
    Measure.restrict_eq_self_of_ae_mem hae]
end DedekindZeta.ConeRadialReduction
