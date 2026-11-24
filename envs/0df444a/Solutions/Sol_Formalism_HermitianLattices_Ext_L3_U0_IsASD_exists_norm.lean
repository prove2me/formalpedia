-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.U0.IsASD.exists_norm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:37:45.837671+00:00
-- url     : https://prove2.me/submissions/0c6e6b69-0a22-4e6f-b45e-9d1374e6a7c1

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsNormRepresentation
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsPrimitiveNorm
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_exists_primitive_norm
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_mul_inv_mem_of_dv
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_IsASD_decomp
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_isUnitIn_of_coprime
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_Dv_eq
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_dv_self_mul
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_exists_norm_of_not_dv
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_exists_norm_of_orth
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_unit_add_dv
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_unit_mul
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_unit_not_dv
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_unit_star

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace Formalism.HermitianLattices.Ext.L3.U0
open WA
variable {K V : Type*} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
variable {S : Subring K} {π : K} {h : V →ₗ⋆[K] V →ₗ[K] K} {W : Submodule K V} {M : AddSubgroup V}
private theorem star_apply_eq_apply_swap_of_isSymm' (hs : h.IsSymm) (x y : V) : star (h x y) = h y x := by
  have h1 := hs.eq x y
  rwa [starRingEnd_apply] at h1
end Formalism.HermitianLattices.Ext.L3.U0
end
end

set_option autoImplicit false
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.U0
open WA
variable {K V : Type*} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
variable {S : Subring K} {π : K} {h : V →ₗ⋆[K] V →ₗ[K] K} {W : Submodule K V} {M : AddSubgroup V}
namespace Formalism.HermitianLattices.Ext.L3.U0
namespace IsASD
theorem _root_.solution (hS : IsHermSemilocal S) (hπ : IsUnif S π) (hs : h.IsSymm)
    (hd : ∀ x, h x x = 0 → x = 0) {z : V} (hM : IsASD S π h W M z) {ξ : V} (hξ : ξ ∈ W) {u : K}
    (hu : IsUnitIn S u) (hξu : h ξ ξ = u) {w₀ : V} (hw₀ : w₀ ∈ M)
    (hw₀u : IsUnitIn S (h w₀ w₀)) : ∃ X ∈ M, h X X = u := by
  obtain ⟨y, hy, _, _, hprim, a, ha, hyy⟩ := exists_primitive_norm hS hd hM.toIsLatIn hξ hu hξu
  have huf : star u = u := by rw [← hξu]; exact star_apply_eq_apply_swap_of_isSymm' hs ξ ξ
  by_cases hex : ∃ w ∈ M, ¬ Dv S π (h w y)
  · obtain ⟨w, hw, hn⟩ := hex
    exact exists_norm_of_not_dv hS hπ hs hM.smul_mem hM.int hy hw ha hu huf hyy hn
  push_neg at hex
  obtain ⟨n₀, hn₀, t, ht, hzn, hye⟩ := hM.decomp hS hπ hs hy hex
  have htu : IsUnitIn S t := isUnitIn_of_coprime hS hπ ht (fun d _ htd hπd => hprim d⁻¹ (by
    rw [hye, smul_add, smul_smul, smul_smul]
    exact M.add_mem (hM.smul_mem _ (by rwa [mul_comm]) _ hn₀)
      (hM.smul_mem _ (by rwa [mul_comm]) _ hM.z_mem)))
  have hnz : h n₀ z = 0 := by rw [← star_apply_eq_apply_swap_of_isSymm' hs z n₀, hzn, star_zero]
  have hexp : h y y = π * π * h n₀ n₀ + star t * t * h z z := by
    rw [hye]
    simp only [map_add, LinearMap.add_apply, LinearMap.map_smulₛₗ₂, map_smul, starRingEnd_apply,
      smul_eq_mul, hzn, hnz, hπ.fix]
    ring
  have hpi : π * π⁻¹ = 1 := mul_inv_cancel₀ hπ.ne
  have hyyU : IsUnitIn S (h y y * π⁻¹) := by
    have e : h y y * π⁻¹ = star t * t * (h z z * π⁻¹) + π * h n₀ n₀ := by
      linear_combination π⁻¹ * hexp + (π * h n₀ n₀) * hpi
    rw [e]
    exact unit_add_dv hπ (unit_mul (unit_mul (unit_star hS htu) htu) hM.z_norm)
      (dv_self_mul hπ (hM.int _ hn₀ _ hn₀))
  have hna : ¬ Dv S π a := by
    intro hda
    obtain ⟨r, hr, rfl⟩ := Dv.eq hπ hda
    have e : h y y * π⁻¹ = π * (star r * r * u) := by
      rw [hyy, star_mul, hπ.fix]
      linear_combination (π * star r * r * u) * hpi
    refine unit_not_dv hπ hyyU ?_
    rw [e]
    exact dv_self_mul hπ (S.mul_mem (S.mul_mem (hS.star_mem r hr) hr) hu.2.1)
  have hN : Dv S π (star a * a) := by
    have huinv : u * u⁻¹ = 1 := mul_inv_cancel₀ hu.1
    have e : star a * a * π⁻¹ = (h y y * π⁻¹) * u⁻¹ := by
      rw [hyy]
      linear_combination (-(star a * a * π⁻¹)) * huinv
    show star a * a * π⁻¹ ∈ S
    rw [e]
    exact S.mul_mem hyyU.2.1 hu.2.2
  have hyy0 : h y y ≠ 0 := fun h0 => hyyU.1 (by rw [h0, zero_mul])
  have hdv : Dv S π (h y w₀) := by
    have h1 := Dv.star hS hπ (hex w₀ hw₀)
    rw [star_apply_eq_apply_swap_of_isSymm' hs] at h1
    exact h1
  obtain ⟨c, hcdef⟩ : ∃ c : K, c = h y w₀ * (h y y)⁻¹ := ⟨_, rfl⟩
  have hcS : c ∈ S := by rw [hcdef]; exact mul_inv_mem_of_dv hπ hdv hyyU
  have hsc : star c = h w₀ y * (h y y)⁻¹ := by
    rw [hcdef, star_mul, star_inv₀, star_apply_eq_apply_swap_of_isSymm' hs, star_apply_eq_apply_swap_of_isSymm' hs, mul_comm]
  have hwM : w₀ - c • y ∈ M := M.sub_mem hw₀ (hM.smul_mem c hcS y hy)
  have hwy : h (w₀ - c • y) y = 0 := by
    simp only [map_sub, LinearMap.sub_apply, LinearMap.map_smulₛₗ₂, starRingEnd_apply,
      smul_eq_mul]
    rw [hsc, mul_assoc, inv_mul_cancel₀ hyy0, mul_one, sub_self]
  have hsc_mul : star c * h y y = h w₀ y := by
    rw [hsc, mul_assoc, inv_mul_cancel₀ hyy0, mul_one]
  have hscS : star c ∈ S := by rw [hsc]; exact mul_inv_mem_of_dv hπ (hex w₀ hw₀) hyyU
  have hww : h (w₀ - c • y) (w₀ - c • y) = h w₀ w₀ + (-(star c * h y w₀)) := by
    simp only [map_sub, LinearMap.sub_apply, LinearMap.map_smulₛₗ₂, map_smul, starRingEnd_apply,
      smul_eq_mul]
    rw [hsc_mul]
    ring
  have hwwU : IsUnitIn S (h (w₀ - c • y) (w₀ - c • y)) := by
    rw [hww]
    refine unit_add_dv hπ hw₀u ?_
    show -(star c * h y w₀) * π⁻¹ ∈ S
    rw [show -(star c * h y w₀) * π⁻¹ = -(star c * (h y w₀ * π⁻¹)) by ring]
    exact S.neg_mem (S.mul_mem hscS hdv)
  exact exists_norm_of_orth hS hπ hs hM.smul_mem hy hwM ha hu huf hyy hna hN hwy hwwU
end IsASD
end Formalism.HermitianLattices.Ext.L3.U0
