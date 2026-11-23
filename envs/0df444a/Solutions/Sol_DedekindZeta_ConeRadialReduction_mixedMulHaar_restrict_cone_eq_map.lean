-- Prove2me | solution 1 for DedekindZeta.ConeRadialReduction.mixedMulHaar_restrict_cone_eq_map
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:43:13.949402+00:00
-- url     : https://prove2.me/submissions/4ba592d2-6084-4c0d-9c20-ed70fd1034f2

import Mathlib
import Definitions.Def_DedekindZeta_Statements
import Definitions.Def_DedekindZeta_MellinPrinciple
import Definitions.Def_DedekindZeta_GammaIntegral
import Definitions.Def_DedekindZeta_ConeRadialReduction
import Theorems.Thm_DedekindZeta_ConeRadialReduction_mem_normEqOneSurface
import Theorems.Thm_DedekindZeta_ConeRadialReduction_continuous_radialMap_uncurry
import Theorems.Thm_DedekindZeta_ConeRadialReduction_surfaceMeasure_apply_compl_normEqOneSurface
import Theorems.Thm_DedekindZeta_ConeRadialReduction_setLIntegral_cone_eq_radial
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
    (DedekindZeta.mixedMulHaar K).restrict (mixedEmbedding.fundamentalCone K)
      = Measure.map (fun p : ℝ × mixedSpace K => radialMap K p.1 p.2)
          (((volume.restrict (Set.Ioi (0 : ℝ))).prod (surfaceMeasure K)).withDensity
            (fun p => ENNReal.ofReal p.1⁻¹)) := by
  -- Two measures agree iff their `lintegral` against every measurable
  -- `ℝ≥0∞`-valued function agrees (`Measure.ext_of_lintegral`).
  refine Measure.ext_of_lintegral _ (fun h hh => ?_)
  haveI : SFinite (DedekindZeta.mixedMulHaar K) := by
    unfold DedekindZeta.mixedMulHaar; infer_instance
  haveI : SFinite (surfaceMeasure K) := by
    unfold surfaceMeasure; infer_instance
  have hF : Measurable (fun p : ℝ × mixedSpace K => radialMap K p.1 p.2) :=
    continuous_radialMap_uncurry.measurable
  have hdens : Measurable (fun p : ℝ × mixedSpace K => ENNReal.ofReal p.1⁻¹) :=
    ENNReal.measurable_ofReal.comp measurable_fst.inv
  -- The surface measure is supported on `normEqOneSurface K`, so a.e. point lies
  -- in it (`surfaceMeasure_apply_compl_normEqOneSurface`).
  have hae : ∀ᵐ σ ∂(surfaceMeasure K), σ ∈ normEqOneSurface K := by
    rw [ae_iff]
    simpa only [Set.mem_compl_iff, Set.compl_def] using
      surfaceMeasure_apply_compl_normEqOneSurface
  -- LHS: rewrite the cone restriction as the proved Lebesgue radial form.
  -- RHS: `lintegral_map` reduces the pushforward, `withDensity` peels off the
  -- `ofReal r⁻¹` weight, and Tonelli (`lintegral_prod`) gives the iterated form.
  have hmprod : Measurable (fun a : ℝ × mixedSpace K => h (radialMap K a.1 a.2)) :=
    hh.comp hF
  rw [setLIntegral_cone_eq_radial h hh, lintegral_map hh hF,
    lintegral_withDensity_eq_lintegral_mul _ hdens hmprod]
  simp only [Pi.mul_apply]
  have hprod := lintegral_prod (μ := volume.restrict (Set.Ioi (0 : ℝ))) (ν := surfaceMeasure K) _ ((hdens.mul hmprod).aemeasurable)
  simp only [Pi.mul_apply] at hprod
  rw [hprod]
  refine lintegral_congr (fun r => ?_)
  -- The inner `σ`-integral: pull out the constant `ofReal r⁻¹` and extend the
  -- surface integral from `normEqOneSurface K` to all of `mixedSpace K`.
  have hmσ : Measurable (fun σ : mixedSpace K => h (radialMap K r σ)) :=
    hh.comp ((continuous_radialMap_uncurry.comp
      (continuous_const.prodMk continuous_id)).measurable)
  rw [lintegral_const_mul _ hmσ, Measure.restrict_eq_self_of_ae_mem hae, mul_comm]
end DedekindZeta.ConeRadialReduction
