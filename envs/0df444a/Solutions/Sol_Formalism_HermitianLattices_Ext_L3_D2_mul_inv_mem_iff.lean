-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.D2.mul_inv_mem_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:29:44.685042+00:00
-- url     : https://prove2.me/submissions/07902f55-d89f-4896-854b-9d2ae87d0420

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_SurjectiveOfNondegenerate
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_RelIndexSSubInfEq
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_IA_phi_apply
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_IA_star_phi
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_FiniteUnitaryColumns_emb_succ_succ
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_FiniteUnitaryColumns_emb_succ_zero
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_FiniteUnitaryColumns_emb_zero_succ
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_FiniteUnitaryColumns_emb_zero_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply
attribute [local simp] Formalism.HermitianLattices.Ext.L3.FiniteUnitaryColumns.emb_succ_succ
attribute [local simp] Formalism.HermitianLattices.Ext.L3.FiniteUnitaryColumns.emb_succ_zero
attribute [local simp] Formalism.HermitianLattices.Ext.L3.FiniteUnitaryColumns.emb_zero_succ
attribute [local simp] Formalism.HermitianLattices.Ext.L3.FiniteUnitaryColumns.emb_zero_zero



set_option autoImplicit false
open NumberField Module
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.D2
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
namespace Formalism.HermitianLattices.Ext.L3.D2
theorem _root_.solution {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) {A B : Submodule (𝓞 K) V} {𝔭 : Ideal (𝓞 F)} {n : ℕ}
    {U W : V ≃ₗ[K] V} (hUA : U ∈ glSub A) (hUB : U ∈ glSub B) (hWA : W ∈ glSub A) (hWB : W ∈ glSub B) :
    U * W⁻¹ ∈ sSub h B 𝔭 n ⊓ glSub A ↔ IA.phi h U - IA.phi h W ∈ hermL B 𝔭 n := by
  have eW : ∀ z : V, W (W⁻¹ z) = z := fun z => by
    rw [← LinearEquiv.mul_apply, mul_inv_cancel]
    rfl
  have eW' : ∀ z : V, W⁻¹ (W z) = z := fun z => by
    rw [← LinearEquiv.mul_apply, inv_mul_cancel]
    rfl
  constructor
  · intro hX
    have hX' := (Subgroup.mem_inf.mp hX).1.2
    refine ⟨fun x y => ?_, fun x hx y hy => ?_⟩
    · simp only [AddSubgroupClass.coe_sub, LinearMap.sub_apply, star_sub, IA.star_phi hs]
    · have := hX' (W x) (apply_mem hWB hx) (W y) (apply_mem hWB hy)
      simp only [LinearEquiv.mul_apply, eW'] at this
      simpa only [LinearMap.sub_apply, IA.phi_apply, sub_sub_sub_cancel_right] using this
  · intro hZ
    refine Subgroup.mem_inf.mpr ⟨⟨mul_mem hUB (inv_mem hWB), fun x hx y hy => ?_⟩,
      mul_mem hUA (inv_mem hWA)⟩
    have := hZ.2 (W⁻¹ x) (apply_mem (inv_mem hWB) hx) (W⁻¹ y) (apply_mem (inv_mem hWB) hy)
    simp only [LinearMap.sub_apply, IA.phi_apply, sub_sub_sub_cancel_right, eW] at this
    simpa only [LinearEquiv.mul_apply] using this
end Formalism.HermitianLattices.Ext.L3.D2
