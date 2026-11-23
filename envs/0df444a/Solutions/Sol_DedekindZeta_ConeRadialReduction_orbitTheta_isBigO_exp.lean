-- Prove2me | solution 1 for DedekindZeta.ConeRadialReduction.orbitTheta_isBigO_exp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:49:31.419037+00:00
-- url     : https://prove2.me/submissions/0bf9a7a8-dbba-4d64-bfc4-3ad1931059e4

import Mathlib
import Definitions.Def_DedekindZeta_Statements
import Definitions.Def_DedekindZeta_MellinPrinciple
import Definitions.Def_DedekindZeta_GammaIntegral
import Definitions.Def_DedekindZeta_ConeRadialReduction
import Theorems.Thm_DedekindZeta_ConeRadialReduction_mem_normEqOneSurface
import Theorems.Thm_DedekindZeta_ConeRadialReduction_measurableSet_normEqOneSurface
import Theorems.Thm_DedekindZeta_ConeRadialReduction_measure_normEqOneSurface_lt_top
import Theorems.Thm_DedekindZeta_ConeRadialReduction_norm_idealThetaKernel_radialMap_isBigO
import Theorems.Thm_DedekindZeta_ConeRadialReduction_integrableOn_mixedThetaKernel_radialMap
import Theorems.Thm_DedekindZeta_Theta_gaussVSchwartz_apply
import Theorems.Thm_DedekindZeta_Theta_idealThetaKernel_eq_mixed
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
theorem _root_.solution (𝔞 : Ideal (𝓞 K)) :
    ∃ c α : ℝ, 0 < c ∧ 0 < α ∧
      (fun r : ℝ => orbitTheta K 𝔞 r) =O[Filter.atTop]
        (fun r : ℝ => Real.exp (-c * r ^ α)) := by
  obtain ⟨c, α, B, hc, hα, hB, hbound⟩ :=
    norm_idealThetaKernel_radialMap_isBigO (K := K) 𝔞
  refine ⟨c, α, hc, hα, ?_⟩
  rw [Asymptotics.isBigO_iff]
  refine ⟨(surfaceMeasure K (normEqOneSurface K)).toReal * B, ?_⟩
  filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with r hr
  have hpos : (0 : ℝ) < r := lt_of_lt_of_le one_pos hr
  -- The orbit kernel is integrable on the surface slice (via the fractional kernel).
  have hint : IntegrableOn
      (fun σ => Theta.idealThetaKernel K 𝔞 (radialMap K r σ))
      (normEqOneSurface K) (surfaceMeasure K) := by
    have h := integrableOn_mixedThetaKernel_radialMap (K := K)
      (𝔞 : FractionalIdeal (𝓞 K)⁰ K) r hpos
    simpa only [← Theta.idealThetaKernel_eq_mixed] using h
  -- The constant `B · exp(-c r^α)` is integrable on the finite-measure slice.
  have hgint : IntegrableOn (fun _ : mixedSpace K => B * Real.exp (-c * r ^ α))
      (normEqOneSurface K) (surfaceMeasure K) :=
    integrableOn_const (measure_normEqOneSurface_lt_top (K := K)).ne
  -- `‖∫‖ ≤ ∫ ‖·‖ ≤ ∫ const = μ(S) · B · exp(-c r^α)`.
  have hnorm_int :
      ∫ σ in normEqOneSurface K,
          ‖Theta.idealThetaKernel K 𝔞 (radialMap K r σ)‖ ∂(surfaceMeasure K)
        ≤ ∫ _σ in normEqOneSurface K, B * Real.exp (-c * r ^ α) ∂(surfaceMeasure K) :=
    setIntegral_mono_on (f := fun σ => ‖Theta.idealThetaKernel K 𝔞 (radialMap K r σ)‖)
      (g := fun _ => B * Real.exp (-c * r ^ α)) hint.norm hgint
      measurableSet_normEqOneSurface (fun σ hσ => hbound r hr σ hσ)
  have hge : (0 : ℝ) ≤ ‖(fun r : ℝ => Real.exp (-c * r ^ α)) r‖ := norm_nonneg _
  calc ‖orbitTheta K 𝔞 r‖
      = ‖∫ σ in normEqOneSurface K,
            Theta.idealThetaKernel K 𝔞 (radialMap K r σ) ∂(surfaceMeasure K)‖ := by
        rw [orbitTheta]
    _ ≤ ∫ σ in normEqOneSurface K,
            ‖Theta.idealThetaKernel K 𝔞 (radialMap K r σ)‖ ∂(surfaceMeasure K) :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ _σ in normEqOneSurface K, B * Real.exp (-c * r ^ α) ∂(surfaceMeasure K) :=
        hnorm_int
    _ = (surfaceMeasure K (normEqOneSurface K)).toReal * (B * Real.exp (-c * r ^ α)) := by
        rw [setIntegral_const, smul_eq_mul, MeasureTheory.measureReal_def]
    _ = (surfaceMeasure K (normEqOneSurface K)).toReal * B
          * ‖(fun r : ℝ => Real.exp (-c * r ^ α)) r‖ := by
        rw [Real.norm_of_nonneg (Real.exp_pos _).le]; ring
end DedekindZeta.ConeRadialReduction
