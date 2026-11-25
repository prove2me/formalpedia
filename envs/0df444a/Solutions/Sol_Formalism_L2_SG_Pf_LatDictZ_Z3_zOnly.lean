-- Prove2me | solution 1 for Formalism.L2.SG.Pf.LatDictZ.Z3.zOnly
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:36:08.813593+00:00
-- url     : https://prove2.me/submissions/8b9907a1-b509-4393-9a27-9d56764a77a8

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_LatDictZAbs
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_LatDictZZLoc
import Theorems.Thm_Formalism_L2_SG_Pf_LatDictZ_Z3_mem_orth
import Theorems.Thm_Formalism_L2_SG_Pf_LatDictZ_Z3_isSelfDualMod_comap
import Theorems.Thm_Formalism_L2_SG_Pf_LatDictZ_Z3_hyz_one
import Theorems.Thm_Formalism_L2_SG_Pf_LatDictZ_Z3_splits_plane
import Theorems.Thm_Formalism_L2_SG_Pf_LatDictZ_Z3_mem_plane
import Theorems.Thm_Formalism_L2_SG_Pf_LatDictZ_Z3_fix_of
import Theorems.Thm_Formalism_L2_SG_Pf_LatDictZ_Z3_isUnitIn_one_sub
import Theorems.Thm_Formalism_L2_SG_Pf_LatDictZ_Z3_exists_dual_one
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_witt_extension_theorem
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
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.LatDictZ Formalism.L2.SG.Pf.LatDictZ.Z3
open ReciprocityTheory.ChartRestriction.L3 ReciprocityTheory.ChartRestriction.L3.WA Formalism.L2.SG.Pf.LatDictZ.Z0
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {h : V →ₗ⋆[K] V →ₗ[K] K}
namespace Formalism.L2.SG.Pf.LatDictZ.Z3
theorem _root_.solution (h1 : SemiGenusLoc) (h2 : PrimPlaneLoc) (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hs : h.IsSymm)
    (hd : ∀ x, (∀ y, h x y = 0) → x = 0) {p : Ideal (𝓞 K)} (hp : p.IsMaximal) (z : V)
    (M₁ M₂ : AddSubgroup V) (hM₁ : IsSelfDualMod (locRing p) h M₁)
    (hM₂ : IsSelfDualMod (locRing p) h M₂) (hz₁ : z ∈ M₁) (hz₂ : z ∈ M₂)
    (hp₁ : ∀ c : K, c • z ∈ M₁ → c ∈ locRing p) (hp₂ : ∀ c : K, c • z ∈ M₂ → c ∈ locRing p) :
    ∃ g ∈ Formalism.HermitianLatticesTheory.isom h, g z = z ∧ ∀ x, x ∈ M₁ ↔ g x ∈ M₂ := by
  have hnzS : h z z ∈ locRing p := hM₁.int _ hz₁ _ hz₁
  have hnzs : star (h z z) = h z z := by
    have e := hs.eq z z
    rwa [starRingEnd_apply] at e
  by_cases hz0 : z = 0
  · obtain ⟨g, hg, hgM⟩ := h1 K V h hK hs hd p hp M₁ M₂ hM₁ hM₂
    exact ⟨g, hg, by rw [hz0, map_zero], hgM⟩
  by_cases hu : IsUnitIn (locRing p) (h z z)
  · have hsp : ∀ {M : AddSubgroup V}, IsSelfDualMod (locRing p) h M → z ∈ M →
        Splits h (Submodule.span K {z}) M := by
      intro M hM hzM w hw
      refine ⟨((h z z)⁻¹ * h z w) • z,
        hM.smul_mem _ ((locRing p).mul_mem hu.2.2 (hM.int _ hzM _ hw)) _ hzM,
        Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self z), ?_⟩
      rw [mem_orth]
      intro q hq
      obtain ⟨d, rfl⟩ := Submodule.mem_span_singleton.mp hq
      have e : h z (w - ((h z z)⁻¹ * h z w) • z) = 0 := by
        rw [map_sub, map_smul, smul_eq_mul, mul_comm ((h z z)⁻¹) _, mul_assoc,
          inv_mul_cancel₀ hu.1, mul_one, sub_self]
      rw [map_smulₛₗ, LinearMap.smul_apply, e, smul_zero]
    obtain ⟨g, hg, hgP, hgM⟩ := fix_of h1 hK hs hd hp (Submodule.span K {z}) hM₁ hM₂
      (hsp hM₁ hz₁) (hsp hM₂ hz₂) (by
        intro w hw
        obtain ⟨d, rfl⟩ := Submodule.mem_span_singleton.mp hw
        exact ⟨fun h' => hM₂.smul_mem _ (hp₁ d h') _ hz₂, fun h' => hM₁.smul_mem _ (hp₂ d h') _ hz₁⟩)
    exact ⟨g, hg, hgP z (Submodule.mem_span_singleton_self z), hgM⟩
  obtain ⟨y₁, hy₁M, hzy₁⟩ := exists_dual_one hK hs hd hp hM₁ hz₁ hp₁ hz0
  have hbS : h y₁ y₁ ∈ locRing p := hM₁.int _ hy₁M _ hy₁M
  have hbs : star (h y₁ y₁) = h y₁ y₁ := by
    have e := hs.eq y₁ y₁
    rwa [starRingEnd_apply] at e
  obtain ⟨y₂, hy₂M, hzy₂, hy₂y₂⟩ :=
    h2 K V h hK hs hd p hp M₂ z (h y₁ y₁) hM₂ hz₂ hp₂ hu hbS hbs ⟨y₁, hzy₁, rfl⟩
  have hD := isUnitIn_one_sub hp.isPrime hnzS hnzs hu hbS
  have hyz₁ := hyz_one hs hzy₁
  have hyz₂ := hyz_one hs hzy₂
  obtain ⟨c, hc⟩ : ∃ c : K, c = (1 - h z z * h y₁ y₁)⁻¹ := ⟨_, rfl⟩
  obtain ⟨v, hvdef⟩ : ∃ v : V, v = star c • z + star (-(c * h z z)) • y₁ := ⟨_, rfl⟩
  have hv : ∀ x, h v x = c * h z x - c * h z z * h y₁ x := by
    intro x
    rw [hvdef]
    simp only [map_add, map_smulₛₗ, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
      starRingEnd_apply, star_star]
    ring
  have hvz : h v z = 0 := by
    rw [hv, hyz₁]
    ring
  have hvy : h v y₁ = 1 := by
    rw [hv, hzy₁]
    have e : c * 1 - c * h z z * h y₁ y₁ = c * (1 - h z z * h y₁ y₁) := by ring
    rw [e, hc, inv_mul_cancel₀ hD.1]
  obtain ⟨T, hTdef⟩ : ∃ T : V →ₗ[K] V, T = LinearMap.id + (h v).smulRight (y₂ - y₁) := ⟨_, rfl⟩
  have hT : ∀ α β : K, T (α • z + β • y₁) = α • z + β • y₂ := by
    intro α β
    have e : h v (α • z + β • y₁) = β := by
      rw [map_add, map_smul, map_smul, hvz, hvy]
      simp
    rw [hTdef, LinearMap.add_apply, LinearMap.id_apply, LinearMap.smulRight_apply, e, smul_sub]
    abel
  have hQ : ∀ x : Submodule.span K ({z, y₁} : Set V), ∃ α β : K, (x : V) = α • z + β • y₁ := by
    intro x
    obtain ⟨α, β, hx⟩ := Submodule.mem_span_pair.mp x.2
    exact ⟨α, β, hx.symm⟩
  have hstar : ∀ x y, star (h x y) = h y x := by
    intro x y
    rw [← starRingEnd_apply]
    exact hs.eq x y
  have hiso : ∀ x y : Submodule.span K ({z, y₁} : Set V),
      h ((T.comp (Submodule.span K ({z, y₁} : Set V)).subtype) x)
        ((T.comp (Submodule.span K ({z, y₁} : Set V)).subtype) y) = h x y := by
    intro x y
    obtain ⟨α, β, hx⟩ := hQ x
    obtain ⟨α', β', hy⟩ := hQ y
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, hx, hy, hT]
    simp only [map_add, map_smulₛₗ, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
      hzy₁, hzy₂, hyz₁, hyz₂, hy₂y₂]
  have hinj : Function.Injective (T.comp (Submodule.span K ({z, y₁} : Set V)).subtype) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx0
    obtain ⟨α, β, hx⟩ := hQ x
    rw [LinearMap.comp_apply, Submodule.subtype_apply, hx, hT] at hx0
    have e1 := congrArg (h z) hx0
    have e2 := congrArg (h y₂) hx0
    simp only [map_add, map_smul, smul_eq_mul, map_zero, hzy₂, hyz₂, hy₂y₂] at e1 e2
    have hβ : β * (1 - h z z * h y₁ y₁) = 0 := by linear_combination e1 - h z z * e2
    have hβ0 : β = 0 := (mul_eq_zero.mp hβ).resolve_right hD.1
    have hα0 : α = 0 := by
      rw [hβ0] at e2
      linear_combination e2
    apply Subtype.ext
    rw [hx, hα0, hβ0]
    simp
  obtain ⟨F, hFi, hFf⟩ := witt_extension_theorem K V h hstar hd _ _ hinj hiso
  have hzQ : z ∈ Submodule.span K ({z, y₁} : Set V) := Submodule.subset_span (by simp)
  have hyQ : y₁ ∈ Submodule.span K ({z, y₁} : Set V) := Submodule.subset_span (by simp)
  have hTz : T z = z := by simpa using hT 1 0
  have hTy : T y₁ = y₂ := by simpa using hT 0 1
  have hFz : F z = z := (hFf ⟨z, hzQ⟩).trans hTz
  have hFy : F y₁ = y₂ := (hFf ⟨y₁, hyQ⟩).trans hTy
  have hmem' : ∀ x, x ∈ M₁.comap F.symm.toLinearMap.toAddMonoidHom ↔ F.symm x ∈ M₁ :=
    fun x => Iff.rfl
  have hM₁' := isSelfDualMod_comap F hFi hM₁
  have hz' : z ∈ M₁.comap F.symm.toLinearMap.toAddMonoidHom := by
    rw [hmem', F.symm_apply_eq.mpr hFz.symm]
    exact hz₁
  have hy' : y₂ ∈ M₁.comap F.symm.toLinearMap.toAddMonoidHom := by
    rw [hmem', F.symm_apply_eq.mpr hFy.symm]
    exact hy₁M
  have hD₂ : IsUnitIn (locRing p) (1 - h z z * h y₂ y₂) := by
    rw [hy₂y₂]
    exact hD
  obtain ⟨g₂, hg₂, hg₂P, hg₂M⟩ := fix_of h1 hK hs hd hp (Submodule.span K {z, y₂}) hM₁' hM₂
    (splits_plane hs hM₁' hz' hy' hzy₂ hD₂) (splits_plane hs hM₂ hz₂ hy₂M hzy₂ hD₂) (by
      intro w hw
      obtain ⟨α, β, rfl⟩ := Submodule.mem_span_pair.mp hw
      rw [mem_plane hs hM₁' hz' hy' hzy₂ hD₂, mem_plane hs hM₂ hz₂ hy₂M hzy₂ hD₂])
  have hg₂' : ∀ x y, h (g₂ x) (g₂ y) = h x y := hg₂
  refine ⟨F.trans g₂, ?_, ?_, ?_⟩
  · intro x y
    change h (g₂ (F x)) (g₂ (F y)) = h x y
    rw [hg₂', hFi]
  · change g₂ (F z) = z
    rw [hFz, hg₂P z (Submodule.subset_span (by simp))]
  · intro x
    change x ∈ M₁ ↔ g₂ (F x) ∈ M₂
    rw [← hg₂M (F x), hmem', F.symm_apply_apply]
end Formalism.L2.SG.Pf.LatDictZ.Z3
