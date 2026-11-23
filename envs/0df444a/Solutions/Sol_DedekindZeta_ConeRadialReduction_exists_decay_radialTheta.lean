-- Prove2me | solution 1 for DedekindZeta.ConeRadialReduction.exists_decay_radialTheta
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:51:25.919934+00:00
-- url     : https://prove2.me/submissions/a6edbcce-ec6b-48a2-9017-2db3c26f5c46

import Mathlib
import Definitions.Def_DedekindZeta_Statements
import Definitions.Def_DedekindZeta_MellinPrinciple
import Definitions.Def_DedekindZeta_GammaIntegral
import Definitions.Def_DedekindZeta_ConeRadialReduction
import Theorems.Thm_DedekindZeta_ConeRadialReduction_mem_normEqOneSurface
import Theorems.Thm_DedekindZeta_ConeRadialReduction_orbitTheta_isBigO_exp
import Theorems.Thm_DedekindZeta_ConeRadialReduction_orbitThetaFrac_isBigO_exp
import Theorems.Thm_DedekindZeta_ConeRadialReduction_exp_isBigO_exp_of_le
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
theorem _root_.solution (𝔞 : Ideal (𝓞 K)) :
    ∃ c α : ℝ, 0 < c ∧ 0 < α ∧
      (fun r : ℝ => radialTheta K 𝔞 r - surfaceVolume K) =O[Filter.atTop]
        (fun r : ℝ => Real.exp (-c * r ^ α)) ∧
      (fun r : ℝ => radialThetaDual K 𝔞 r - surfaceVolume K) =O[Filter.atTop]
        (fun r : ℝ => Real.exp (-c * r ^ α)) := by
  obtain ⟨c₁, α₁, hc₁, hα₁, hf⟩ := orbitTheta_isBigO_exp (K := K) 𝔞
  obtain ⟨c₂, α₂, hc₂, hα₂, hg⟩ := orbitThetaFrac_isBigO_exp (K := K) (Theta.dualIdeal K 𝔞)
  refine ⟨min c₁ c₂, min α₁ α₂, lt_min hc₁ hc₂, lt_min hα₁ hα₂, ?_, ?_⟩
  · have hsimp : (fun r : ℝ => radialTheta K 𝔞 r - surfaceVolume K)
        = (fun r : ℝ => orbitTheta K 𝔞 r) := by
      funext r; simp [radialTheta, add_sub_cancel_right]
    rw [hsimp]
    exact hf.trans
      (exp_isBigO_exp_of_le (lt_min hc₁ hc₂) (min_le_left _ _) (min_le_left _ _))
  · have hsimp : (fun r : ℝ => radialThetaDual K 𝔞 r - surfaceVolume K)
        = (fun r : ℝ => orbitThetaFrac K (Theta.dualIdeal K 𝔞) r) := by
      funext r; simp [radialThetaDual, add_sub_cancel_right]
    rw [hsimp]
    exact hg.trans
      (exp_isBigO_exp_of_le (lt_min hc₁ hc₂) (min_le_right _ _) (min_le_right _ _))
end DedekindZeta.ConeRadialReduction
