-- Prove2me | solution 1 for DedekindZeta.ConeRadialReduction.orbitThetaFrac_isBigO_exp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:49:32.013246+00:00
-- url     : https://prove2.me/submissions/0200eb5d-13fc-4b2f-b845-966431de4fc0

import Mathlib
import Definitions.Def_DedekindZeta_Statements
import Definitions.Def_DedekindZeta_MellinPrinciple
import Definitions.Def_DedekindZeta_GammaIntegral
import Definitions.Def_DedekindZeta_ConeRadialReduction
import Theorems.Thm_DedekindZeta_ConeRadialReduction_mem_normEqOneSurface
import Theorems.Thm_DedekindZeta_ConeRadialReduction_measurableSet_normEqOneSurface
import Theorems.Thm_DedekindZeta_ConeRadialReduction_measure_normEqOneSurface_lt_top
import Theorems.Thm_DedekindZeta_ConeRadialReduction_integrableOn_mixedThetaKernel_radialMap
import Theorems.Thm_DedekindZeta_ConeRadialReduction_mixedThetaKernel_radialMap_isBigO_uniform
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
theorem _root_.solution (I : FractionalIdeal (𝓞 K)⁰ K) :
    ∃ c α : ℝ, 0 < c ∧ 0 < α ∧
      (fun r : ℝ => orbitThetaFrac K I r) =O[Filter.atTop]
        (fun r : ℝ => Real.exp (-c * r ^ α)) := by
  obtain ⟨c, α, B, hc, hα, hB, hbound⟩ :=
    mixedThetaKernel_radialMap_isBigO_uniform (K := K) I
  refine ⟨c, α, hc, hα, ?_⟩
  rw [Asymptotics.isBigO_iff]
  refine ⟨B * (surfaceMeasure K (normEqOneSurface K)).toReal, ?_⟩
  filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with r hr
  have hr0 : (0 : ℝ) < r := lt_of_lt_of_le zero_lt_one hr
  have hfin : surfaceMeasure K (normEqOneSurface K) < ⊤ :=
    measure_normEqOneSurface_lt_top
  -- Integrability of the kernel on the surface slice (sibling lemma).
  have hintker : IntegrableOn
      (fun σ => Theta.mixedThetaKernel K I (radialMap K r σ))
      (normEqOneSurface K) (surfaceMeasure K) :=
    integrableOn_mixedThetaKernel_radialMap I r hr0
  -- `‖∫ Θ‖ ≤ ∫ ‖Θ‖`.
  have hnorm_le : ‖orbitThetaFrac K I r‖
      ≤ ∫ σ in normEqOneSurface K,
          ‖Theta.mixedThetaKernel K I (radialMap K r σ)‖ ∂(surfaceMeasure K) := by
    rw [orbitThetaFrac]
    exact norm_integral_le_integral_norm _
  -- `∫ ‖Θ‖ ≤ ∫ (B·e^{-c r^α}) = μ_S(S)·B·e^{-c r^α}`.
  have hmono : ∫ σ in normEqOneSurface K,
        ‖Theta.mixedThetaKernel K I (radialMap K r σ)‖ ∂(surfaceMeasure K)
      ≤ ∫ _σ in normEqOneSurface K, B * Real.exp (-c * r ^ α) ∂(surfaceMeasure K) := by
    refine setIntegral_mono_on hintker.norm ?_ measurableSet_normEqOneSurface ?_
    · exact integrableOn_const hfin.ne
    · intro σ hσ; exact hbound r hr σ hσ
  have hconst : ∫ _σ in normEqOneSurface K, B * Real.exp (-c * r ^ α)
        ∂(surfaceMeasure K)
      = (surfaceMeasure K (normEqOneSurface K)).toReal * (B * Real.exp (-c * r ^ α)) := by
    rw [setIntegral_const]
    simp [MeasureTheory.measureReal_def, smul_eq_mul]
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  calc ‖orbitThetaFrac K I r‖
      ≤ ∫ σ in normEqOneSurface K,
          ‖Theta.mixedThetaKernel K I (radialMap K r σ)‖ ∂(surfaceMeasure K) := hnorm_le
    _ ≤ (surfaceMeasure K (normEqOneSurface K)).toReal * (B * Real.exp (-c * r ^ α)) :=
        hmono.trans_eq hconst
    _ = B * (surfaceMeasure K (normEqOneSurface K)).toReal * Real.exp (-c * r ^ α) := by
        ring
end DedekindZeta.ConeRadialReduction
