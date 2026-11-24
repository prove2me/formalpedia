-- Prove2me | solution 1 for Formalism.L2.Fam.IdTrans.unrAE
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:11:52.533883+00:00
-- url     : https://prove2.me/submissions/1e2fc63b-a9ae-4a7c-850d-48bdeb7c5c6c

import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_IsUnitaryNormOf
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_UnrAe
import Definitions.Def_Formalism_LocalToGlobal_NumberFieldFamilies_IdTransSM
import Theorems.Thm_Formalism_L2_Fam_IdTrans_eq_one_of_pow
import Theorems.Thm_Formalism_L2_Fam_IdTrans_single_mem_nhds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.L2.Host Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Filter Topology
open Formalism Formalism.L2 Formalism.L2.Fam Formalism.L2.Fam.IdTrans
namespace Formalism.L2.Fam.IdTrans
theorem _root_.solution {L : Type} [Field L] [NumberField L] : UnrAE L := by
  intro χ hχ
  classical
  set W : Set ℂˣ := {z | ‖(z : ℂ) - 1‖ < 1} with hWdef
  have hWo : IsOpen W := isOpen_lt (continuous_norm.comp (Units.continuous_val.sub continuous_const)) continuous_const
  have hW1 : (1 : ℂˣ) ∈ W := by simp [hWdef]
  have hN : χ ⁻¹' W ∈ 𝓝 (1 : Ideles L) := by
    apply hχ.continuousAt.preimage_mem_nhds
    rw [map_one]
    exact hWo.mem_nhds hW1
  rw [(Units.isEmbedding_embedProduct (M := AdeleRing (𝓞 L) L)).isInducing.nhds_eq_comap] at hN
  obtain ⟨T, hT, hTN⟩ := hN
  rw [map_one] at hT
  have hT' : T ∈ 𝓝 (((1 : AdeleRing (𝓞 L) L), (1 : (AdeleRing (𝓞 L) L)ᵐᵒᵖ))) := hT
  obtain ⟨T1, hT1, T2, hT2, hT12⟩ := mem_nhds_prod_iff.mp hT'
  have hT2' : MulOpposite.op ⁻¹' T2 ∈ 𝓝 (1 : AdeleRing (𝓞 L) L) :=
    MulOpposite.continuous_op.continuousAt.preimage_mem_nhds (by rw [MulOpposite.op_one]; exact hT2)
  obtain ⟨I1, hI1, h1⟩ := single_mem_nhds hT1
  obtain ⟨I2, hI2, h2⟩ := single_mem_nhds hT2'
  have hmem : ∀ v ∉ I1 ∪ I2, ∀ x : (v.adicCompletion L)ˣ, IsUnitAt v x → χ (localIdele L v x) ∈ W := by
    intro v hv x hx
    have hv1 : v ∉ I1 := fun h => hv (Or.inl h)
    have hv2 : v ∉ I2 := fun h => hv (Or.inr h)
    have hxO : (x : v.adicCompletion L) ∈ v.adicCompletionIntegers L := by
      rw [HeightOneSpectrum.mem_adicCompletionIntegers]; exact le_of_eq hx
    have hxO' : ((x⁻¹ : (v.adicCompletion L)ˣ) : v.adicCompletion L) ∈ v.adicCompletionIntegers L := by
      rw [HeightOneSpectrum.mem_adicCompletionIntegers, Units.val_inv_eq_inv_val, map_inv₀]
      rw [show Valued.v (x : v.adicCompletion L) = 1 from hx, inv_one]
    apply hTN
    apply hT12
    refine ⟨h1 v hv1 _ hxO, ?_⟩
    show (((localIdele L v x)⁻¹ : Ideles L) : AdeleRing (𝓞 L) L) ∈ MulOpposite.op ⁻¹' T2
    rw [← map_inv]
    exact h2 v hv2 _ hxO'
  refine Filter.mem_of_superset (hI1.union hI2).compl_mem_cofinite fun v hv x hx => ?_
  apply Units.ext
  apply eq_one_of_pow _ (Units.ne_zero _)
  intro n
  have hxn : IsUnitAt v (x ^ n) := by
    show Valued.v (((x ^ n : (v.adicCompletion L)ˣ)) : v.adicCompletion L) = 1
    rw [Units.val_zpow_eq_zpow_val, map_zpow₀, show Valued.v (x : v.adicCompletion L) = 1 from hx, one_zpow]
  have := hmem v hv (x ^ n) hxn
  rw [map_zpow, map_zpow] at this
  have h' : ‖(((χ (localIdele L v x)) ^ n : ℂˣ) : ℂ) - 1‖ < 1 := this
  rwa [Units.val_zpow_eq_zpow_val] at h'
end Formalism.L2.Fam.IdTrans
