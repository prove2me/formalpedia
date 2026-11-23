-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.U0.IsASD.cut
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:27:48.692168+00:00
-- url     : https://prove2.me/submissions/75db6ca3-8e01-4e28-969b-fc1dc0f952d2

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsPrimitiveNorm
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsIsomScale
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_mem_cutW
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_mem_cutM
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_symm_zero
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_proj_mem
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_IsLatIn_cut
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_int_of_cut
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_IsSD_cut
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_Dv_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.U0
open WA
variable {K V : Type*} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
variable {S : Subring K} {π : K} {h : V →ₗ⋆[K] V →ₗ[K] K} {W : Submodule K V} {M : AddSubgroup V}
namespace Formalism.HermitianLattices.Ext.L3.U0
namespace IsASD
theorem _root_.solution (hS : IsHermSemilocal S) (hπ : IsUnif S π) (hs : h.IsSymm) {z : V}
    (hM : IsASD S π h W M z) {X : V} (hX : X ∈ M) (hu : IsUnitIn S (h X X)) :
    IsASD S π h (cutW h W X) (cutM h M X) (z - (h X z * (h X X)⁻¹) • X) := by
  have hL := hM.toIsLatIn
  have hXz' := (mem_cutM.1 (proj_mem hL hX hu hM.z_mem)).2
  have hsh : ∀ v, h X v = 0 → h (z - (h X z * (h X X)⁻¹) • X) v = h z v := by
    intro v hv
    rw [LinearMap.map_sub₂, LinearMap.map_smulₛₗ₂, hv, smul_zero, sub_zero]
  refine ⟨hL.cut X, proj_mem hL hX hu hM.z_mem, ?_, fun m hm => ?_, fun x hx hzx hxS => ?_⟩
  · obtain ⟨hN0, -, hNi⟩ := hu
    obtain ⟨hu0, hu1, hui⟩ := hM.z_norm
    have hπ0 := hπ.ne
    obtain ⟨s, hsS, hzX⟩ : ∃ s ∈ S, h z X = s * π :=
      ⟨_, hM.z_rad X hX, by rw [inv_mul_cancel_right₀ hπ0]⟩
    have hXz : h X z = star s * π := by
      rw [← hs.eq z X, hzX, map_mul, starRingEnd_apply, starRingEnd_apply, hπ.fix]
    have hNN : starRingEnd K (h X X) = h X X := hs.eq X X
    have e1 : h (z - (h X z * (h X X)⁻¹) • X) X = 0 := symm_zero hs hXz'
    have key : h (z - (h X z * (h X X)⁻¹) • X) (z - (h X z * (h X X)⁻¹) • X)
        = h z z - s * π * (h X X)⁻¹ * (star s * π) := by
      rw [LinearMap.map_sub, LinearMap.map_smul, e1, smul_zero, sub_zero, LinearMap.map_sub₂,
        LinearMap.map_smulₛₗ₂, smul_eq_mul, map_mul, map_inv₀, hNN, hs.eq X z, hzX, hXz]
    have hzz0 : h z z ≠ 0 := fun e => hu0 (by rw [e, zero_mul])
    have hmul : ∀ a b : K, IsUnitIn S a → IsUnitIn S b → IsUnitIn S (a * b) := fun a b ha hb =>
      ⟨mul_ne_zero ha.1 hb.1, S.mul_mem ha.2.1 hb.2.1, by rw [mul_inv]; exact S.mul_mem ha.2.2 hb.2.2⟩
    have e2 : (h z z - s * π * (h X X)⁻¹ * (star s * π)) * π⁻¹
        = (h z z * π⁻¹) * (1 + π * (-(s * star s * (h X X)⁻¹) * (h z z * π⁻¹)⁻¹)) := by
      field_simp
      ring
    rw [key, e2]
    exact hmul _ _ ⟨hu0, hu1, hui⟩ (hπ.rad _ (S.mul_mem (S.neg_mem
      (S.mul_mem (S.mul_mem hsS (hS.star_mem s hsS)) hNi)) hui))
  · rw [mem_cutM] at hm
    show h _ m * π⁻¹ ∈ S
    rw [hsh m hm.2]
    exact hM.z_rad m hm.1
  · obtain ⟨hxW, hx0⟩ := mem_cutW.1 hx
    rw [hsh x hx0] at hzx
    exact mem_cutM.2 ⟨hM.dual x hxW hzx (int_of_cut hL hX hu hx0 hxS), hx0⟩
end IsASD
end Formalism.HermitianLattices.Ext.L3.U0
