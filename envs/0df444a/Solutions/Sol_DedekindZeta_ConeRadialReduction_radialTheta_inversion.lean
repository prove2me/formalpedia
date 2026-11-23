-- Prove2me | solution 1 for DedekindZeta.ConeRadialReduction.radialTheta_inversion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:55:09.192407+00:00
-- url     : https://prove2.me/submissions/df5d4942-b52b-400d-a7b5-f91413743c9a

import Mathlib
import Definitions.Def_DedekindZeta_Statements
import Definitions.Def_DedekindZeta_MellinPrinciple
import Definitions.Def_DedekindZeta_GammaIntegral
import Definitions.Def_DedekindZeta_ConeRadialReduction
import Theorems.Thm_DedekindZeta_ConeRadialReduction_mem_normEqOneSurface
import Theorems.Thm_DedekindZeta_ConeRadialReduction_measurableSet_normEqOneSurface
import Theorems.Thm_DedekindZeta_ConeRadialReduction_norm_radialMap_of_mem
import Theorems.Thm_DedekindZeta_ConeRadialReduction_measure_normEqOneSurface_lt_top
import Theorems.Thm_DedekindZeta_ConeRadialReduction_integrableOn_mixedThetaKernel_radialMap
import Theorems.Thm_DedekindZeta_ConeRadialReduction_orbitTheta_inv_apply
import Theorems.Thm_DedekindZeta_Theta_gaussVSchwartz_apply
import Theorems.Thm_DedekindZeta_Theta_idealThetaKernel_inversion
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
theorem _root_.solution (𝔞 : Ideal (𝓞 K)) (hne : 𝔞 ≠ 0) (r : ℝ) (hr : 0 < r) :
    radialTheta K 𝔞 (1 / r)
      = (Theta.covolume K 𝔞 : ℂ)⁻¹ * ((r ^ (1 : ℝ) : ℝ) : ℂ) * radialThetaDual K 𝔞 r := by
  -- Abbreviation for the inversion constant `c = r / covol 𝔞`.
  set c : ℂ := ((r / Theta.covolume K 𝔞 : ℝ) : ℂ) with hc
  -- Finiteness of the surface measure ⇒ constants are integrable on `S`.
  haveI : IsFiniteMeasure ((surfaceMeasure K).restrict (normEqOneSurface K)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_normEqOneSurface_lt_top⟩
  -- Pointwise: the inverted kernel equals `c·Θ_mix(dual) + (c − 1)` on `S`.
  have hcongr : Set.EqOn
      (fun σ => Theta.idealThetaKernel K 𝔞 (radialMap K r σ)⁻¹)
      (fun σ => c * Theta.mixedThetaKernel K (Theta.dualIdeal K 𝔞) (radialMap K r σ)
          + (c - 1))
      (normEqOneSurface K) := by
    intro σ hσ
    have hxr : mixedEmbedding.norm (radialMap K r σ) = r := norm_radialMap_of_mem r hr hσ
    have hxne : mixedEmbedding.norm (radialMap K r σ) ≠ 0 := by rw [hxr]; exact hr.ne'
    show Theta.idealThetaKernel K 𝔞 (radialMap K r σ)⁻¹ = _
    rw [hc, Theta.idealThetaKernel_inversion K 𝔞 hne _ hxne, hxr, abs_of_pos hr]
    ring
  -- Integrability of the two pieces.
  have hint1 : Integrable
      (fun σ => c * Theta.mixedThetaKernel K (Theta.dualIdeal K 𝔞) (radialMap K r σ))
      ((surfaceMeasure K).restrict (normEqOneSurface K)) :=
    (integrableOn_mixedThetaKernel_radialMap (Theta.dualIdeal K 𝔞) r hr).const_mul c
  have hint2 : Integrable (fun _ : mixedSpace K => c - 1)
      ((surfaceMeasure K).restrict (normEqOneSurface K)) := integrable_const _
  -- Assemble.
  simp only [radialTheta]
  rw [orbitTheta_inv_apply 𝔞 r hr,
    setIntegral_congr_fun measurableSet_normEqOneSurface hcongr,
    integral_add hint1 hint2, integral_const_mul, setIntegral_const,
    Complex.real_smul, Real.rpow_one]
  simp only [radialThetaDual, orbitThetaFrac, surfaceVolume, hc,
    MeasureTheory.measureReal_def]
  push_cast [Complex.ofReal_div]
  ring
end DedekindZeta.ConeRadialReduction
