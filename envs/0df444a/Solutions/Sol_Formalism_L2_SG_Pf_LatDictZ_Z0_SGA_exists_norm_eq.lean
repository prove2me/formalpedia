-- Prove2me | solution 1 for Formalism.L2.SG.Pf.LatDictZ.Z0.SGA.exists_norm_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:19:57.778401+00:00
-- url     : https://prove2.me/submissions/d36baf97-8195-4d7d-b9a8-c7e2e21e00b1

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_LatDictZAbs
import Definitions.Def_Formalism_SelfDualUnimodular_LocalLatticeDictionary_ExistsUnitNorm
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L3_WA_exists_norm_one_mul_mem
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L3_WA_exists_norm_one_of_pair
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L3_WA_isHermSemilocal_locRing
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
noncomputable section
open NumberField
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.LatDictZ Formalism.L2.SG.Pf.LatDictZ.Z0 Formalism.L2.SG.Pf.LatDictZ.Z0.SGA
open ReciprocityTheory.ChartRestriction.L3 ReciprocityTheory.ChartRestriction.L3.WA
variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable {V : Type} [AddCommGroup V] [Module K V]
namespace Formalism.L2.SG.Pf.LatDictZ.Z0.SGA
theorem _root_.solution {p : Ideal (𝓞 K)} (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hp : p.IsMaximal)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hnd : ∀ x, (∀ y, h x y = 0) → x = 0)
    {M : AddSubgroup V} (hM : IsSelfDualMod (locRing p) h M) (e : V)
    (he : IsUnitIn (locRing p) (h e e)) :
    ∃ X ∈ M, h X X = h e e := by
  have hS := isHermSemilocal_locRing hK hp
  set S := locRing p with hSdef
  have hsym : ∀ u v, star (h u v) = h v u := fun u v => hs.eq u v
  set a := h e e with ha
  have hafix : star a = a := hsym e e
  obtain ⟨ha0, haS, hainv⟩ := he
  have he0 : e ≠ 0 := by rintro rfl; simp [a] at ha0
  obtain ⟨y, hy⟩ : ∃ y, h e y ≠ 0 := by
    by_contra hc; push Not at hc; exact he0 (hnd e hc)
  obtain ⟨t', ht'0, ht'M⟩ := hM.span y
  obtain ⟨t, ht0, htM⟩ := hM.span e
  let f : V →+ K :=
    { toFun := fun u => h u e
      map_zero' := by simp
      map_add' := by intro a b; simp }
  have hf : ∀ u, f u = h u e := fun _ => rfl
  have hAS : ∀ c ∈ S, ∀ a ∈ M.map f, c * a ∈ M.map f := by
    rintro c hc _ ⟨u, hu, rfl⟩
    refine ⟨star c • u, hM.smul_mem _ (hS.star_mem _ hc) _ hu, ?_⟩
    rw [hf, hf, map_smulₛₗ, LinearMap.smul_apply, starRingEnd_apply, star_star, smul_eq_mul]
  have h0 : ∃ a ∈ M.map f, a ≠ 0 := by
    refine ⟨_, ⟨t' • y, ht'M, rfl⟩, ?_⟩
    rw [hf, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply, ← hsym e y]
    exact mul_ne_zero (star_ne_zero.mpr ht'0) (star_ne_zero.mpr hy)
  have hb : ∀ a ∈ M.map f, t * a ∈ S := by
    rintro _ ⟨u, hu, rfl⟩
    have := hM.int u hu _ htM
    rwa [map_smul, smul_eq_mul] at this
  obtain ⟨α, ⟨w₀, hw₀, hα⟩, hα0, hdiv⟩ := hS.principal (M.map f) hAS h0 ⟨t, ht0, hb⟩
  rw [hf] at hα
  have hyM : α⁻¹ • e ∈ M := by
    apply hM.dual
    intro u hu
    have := hdiv _ ⟨u, hu, rfl⟩
    rw [map_smul, smul_eq_mul, mul_comm]
    exact this
  have hyw : h (α⁻¹ • e) w₀ = 1 := by
    rw [map_smulₛₗ, LinearMap.smul_apply, ← hsym w₀ e, hα, starRingEnd_apply, smul_eq_mul,
      ← star_mul', inv_mul_cancel₀ hα0, star_one]
  have hyy : h (α⁻¹ • e) (α⁻¹ • e) = star α⁻¹ * α⁻¹ * a := by
    rw [map_smul, map_smulₛₗ, LinearMap.smul_apply, starRingEnd_apply, smul_eq_mul, smul_eq_mul]
    ring
  let h' : V →ₗ⋆[K] V →ₗ[K] K := a⁻¹ • h
  have h'app : ∀ u v, h' u v = a⁻¹ * h u v := fun u v => by
    show (a⁻¹ • h) u v = _
    rw [LinearMap.smul_apply, LinearMap.smul_apply, smul_eq_mul]
  have hs' : h'.IsSymm := by
    refine ⟨fun u v => ?_⟩
    rw [h'app, h'app, map_mul, starRingEnd_apply, starRingEnd_apply, star_inv₀, hafix, hsym u v]
  have hnorm : star α⁻¹ * α⁻¹ ∈ S := by
    have : star α⁻¹ * α⁻¹ = h (α⁻¹ • e) (α⁻¹ • e) * a⁻¹ := by rw [hyy]; field_simp
    rw [this]; exact S.mul_mem (hM.int _ hyM _ hyM) hainv
  obtain ⟨bb, hbb1, hbbS⟩ := exists_norm_one_mul_mem hS (a := α⁻¹) hnorm
  have hbb0 : bb ≠ 0 := by rintro rfl; simp at hbb1
  have hyy' : h' (α⁻¹ • e) (α⁻¹ • e) = star (α⁻¹ * bb) * (α⁻¹ * bb) := by
    rw [h'app, hyy, star_mul']
    calc a⁻¹ * (star α⁻¹ * α⁻¹ * a) = star α⁻¹ * α⁻¹ * (star bb * bb) := by
          rw [hbb1]; field_simp
      _ = _ := by ring
  have hwM : a • w₀ ∈ M := hM.smul_mem _ haS _ hw₀
  have hyw' : h' (α⁻¹ • e) (a • w₀) = 1 := by
    rw [h'app, map_smul, smul_eq_mul, hyw]; field_simp
  have hww : h' (a • w₀) (a • w₀) ∈ S := by
    rw [h'app, map_smul, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul, starRingEnd_apply,
      hafix]
    have : a⁻¹ * (a * (a * h w₀ w₀)) = a * h w₀ w₀ := by field_simp
    rw [this]; exact S.mul_mem haS (hM.int _ hw₀ _ hw₀)
  obtain ⟨c, hc, d, hd, hcd⟩ := exists_norm_one_of_pair hS hs' hbbS
    (mul_ne_zero (inv_ne_zero hα0) hbb0) hyy' hyw' hww
  refine ⟨c • (a • w₀) + d • (α⁻¹ • e), M.add_mem (hM.smul_mem _ hc _ hwM) (hM.smul_mem _ hd _ hyM), ?_⟩
  rw [h'app] at hcd
  have := congrArg (fun u => a * u) hcd
  rw [← mul_assoc, mul_inv_cancel₀ ha0, one_mul, mul_one] at this
  exact this
end Formalism.L2.SG.Pf.LatDictZ.Z0.SGA
