-- Prove2me | solution 1 for DedekindZeta.ConeMellinBridge.conePolarCorrection_residue_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:46:58.033623+00:00
-- url     : https://prove2.me/submissions/f6953aec-2640-412e-ad8c-40fead8315b7

import Mathlib
import Definitions.Def_DedekindZeta_Statements
import Definitions.Def_DedekindZeta_MellinPrinciple
import Definitions.Def_DedekindZeta_ConeRadialReduction
import Definitions.Def_DedekindZeta_ConeMellinBridge
import Theorems.Thm_DedekindZeta_ConeRadialReduction_mem_normEqOneSurface
import Theorems.Thm_DedekindZeta_Theta_gaussVSchwartz_apply
import Theorems.Thm_DedekindZeta_Theta_mixedGaussianSchwartz_apply
attribute [local simp] DedekindZeta.ConeRadialReduction.mem_normEqOneSurface
attribute [local simp] DedekindZeta.Theta.gaussVSchwartz_apply
attribute [local simp] DedekindZeta.Theta.mixedGaussianSchwartz_apply



set_option autoImplicit true
open MeasureTheory NumberField NumberField.mixedEmbedding
open scoped Real nonZeroDivisors
open DedekindZeta DedekindZeta.ConeMellinBridge
open DedekindZeta.ConeRadialReduction DedekindZeta.MellinPrinciple
variable (K : Type*) [Field K] [NumberField K]
variable {K}
variable (K)
namespace DedekindZeta.ConeMellinBridge
theorem _root_.solution (𝔞 : Ideal (𝓞 K)) :
    Filter.Tendsto (fun s : ℂ => (s - 1) * conePolarCorrection K 𝔞 s)
      (nhdsWithin 1 {(1 : ℂ)}ᶜ)
      (nhds ((Theta.covolume K 𝔞 : ℂ)⁻¹ * surfaceVolume K)) := by
  set C : ℂ := (Theta.covolume K 𝔞 : ℂ)⁻¹ with hC
  set V : ℂ := surfaceVolume K with hV
  have hcont : ContinuousAt (fun s : ℂ => (s - 1) * (-V / s) + C * V) 1 := by
    refine (((continuousAt_id.sub continuousAt_const).mul ?_).add continuousAt_const)
    exact continuousAt_const.div continuousAt_id (by norm_num)
  have hψ : Filter.Tendsto (fun s : ℂ => (s - 1) * (-V / s) + C * V)
      (nhdsWithin 1 {(1 : ℂ)}ᶜ) (nhds (C * V)) := by
    have h1 := hcont.tendsto.mono_left
      (nhdsWithin_le_nhds : nhdsWithin (1 : ℂ) {(1 : ℂ)}ᶜ ≤ nhds 1)
    convert h1 using 2
    simp
  refine hψ.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs1 : s ≠ 1 := hs
  have hs10 : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  have hcancel : (s - 1) * (C * V / (s - 1)) = C * V := by
    rw [mul_div_assoc']; exact mul_div_cancel_left₀ _ hs10
  unfold conePolarCorrection
  rw [mul_add, hcancel]
end DedekindZeta.ConeMellinBridge
