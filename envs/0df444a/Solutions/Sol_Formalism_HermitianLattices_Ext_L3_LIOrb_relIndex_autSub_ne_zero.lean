-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.LIOrb.relIndex_autSub_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:59:10.152849+00:00
-- url     : https://prove2.me/submissions/a907d5a5-a076-47ce-9ae1-9c567dc8e81b

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_FormRightMem
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_RelIndexEqOfCover
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsMulDvdUnif
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ApplyMemSmulOfMemAutSub
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LIOrb_apply_mem_smul_of_mem_autSub
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LIOrb_exists_congr_mem_autSub
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LIOrb_relIndex_ne_zero_of_map
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LIOrb_sub_mem_of_redA_eq
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LIOrb_finite_quot
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_idealPowerSpanBounds_finite_quot


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module Filter
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.LIOrb
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
namespace Formalism.HermitianLattices.Ext.L3.LIOrb
theorem _root_.solution (h : V →ₗ⋆[K] V →ₗ[K] K) {M₁ M₂ : Submodule (𝓞 K) V}
    (hM₁ : Submodule.IsLattice K M₁) (hM₂ : Submodule.IsLattice K M₂) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) :
    (autSub h (locF 𝔭 M₂)).relIndex (autSub h (locF 𝔭 M₁)) ≠ 0 := by
  obtain ⟨j, hj⟩ := exists_congr_mem_autSub h hM₁ hM₂ h𝔭
  have := finite_quot hM₁ h𝔭 j
  have : Finite ((↥(locF 𝔭 M₁) ⧸ ((extP K 𝔭) ^ j • ⊤ : Submodule (𝓞 K) ↥(locF 𝔭 M₁))) →ₗ[𝓞 K]
      (↥(locF 𝔭 M₁) ⧸ ((extP K 𝔭) ^ j • ⊤ : Submodule (𝓞 K) ↥(locF 𝔭 M₁)))) :=
    Finite.of_injective _ DFunLike.coe_injective
  refine relIndex_ne_zero_of_map _ _ (redA (extP K 𝔭 ^ j)) fun a b e => ?_
  refine hj j le_rfl _ (mul_mem (inv_mem a.2) b.2) fun z hz => ?_
  have h1 := apply_mem_smul_of_mem_autSub (inv_mem a.2) _ (sub_mem_of_redA_eq _ e hz)
  have h2 : ((a : V ≃ₗ[K] V)⁻¹ * (b : V ≃ₗ[K] V)) z - z =
      (a : V ≃ₗ[K] V)⁻¹ ((b : V ≃ₗ[K] V) z - (a : V ≃ₗ[K] V) z) := by
    rw [map_sub]
    change _ = (a : V ≃ₗ[K] V).symm _ - (a : V ≃ₗ[K] V).symm _
    rw [LinearEquiv.symm_apply_apply]
    rfl
  rw [h2]
  exact h1
end Formalism.HermitianLattices.Ext.L3.LIOrb
