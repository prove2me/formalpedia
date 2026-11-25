-- Prove2me | solution 1 for Formalism.L2.SG.Pf.LatDictZ.Z3.exists_dual_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:19:31.077502+00:00
-- url     : https://prove2.me/submissions/2d43b425-0998-4886-b630-f758883df2ab

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_LatDictZAbs
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_LatDictZZLoc
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
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
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.LatDictZ Formalism.L2.SG.Pf.LatDictZ.Z3
open ReciprocityTheory.ChartRestriction.L3 ReciprocityTheory.ChartRestriction.L3.WA Formalism.L2.SG.Pf.LatDictZ.Z0
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {h : V →ₗ⋆[K] V →ₗ[K] K}
namespace Formalism.L2.SG.Pf.LatDictZ.Z3
theorem _root_.solution (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hs : h.IsSymm)
    (hd : ∀ x, (∀ y, h x y = 0) → x = 0) {p : Ideal (𝓞 K)} (hp : p.IsMaximal) {z : V}
    {M₁ : AddSubgroup V} (hM₁ : IsSelfDualMod (locRing p) h M₁) (hz₁ : z ∈ M₁)
    (hp₁ : ∀ c : K, c • z ∈ M₁ → c ∈ locRing p) (hz0 : z ≠ 0) : ∃ y₁ ∈ M₁, h z y₁ = 1 := by
  have hS := isHermSemilocal_locRing hK hp
  let f : V →+ K :=
    { toFun := fun m => h m z
      map_zero' := by simp
      map_add' := fun a b => by simp }
  have hfA : ∀ a, a ∈ M₁.map f ↔ ∃ m ∈ M₁, h m z = a := fun a => AddSubgroup.mem_map
  have H1 : ∀ s ∈ locRing p, ∀ a ∈ M₁.map f, s * a ∈ M₁.map f := by
    intro s hs' a ha
    obtain ⟨m, hm, rfl⟩ := (hfA a).mp ha
    refine (hfA _).mpr ⟨star s • m, hM₁.smul_mem _ (hS.star_mem _ hs') _ hm, ?_⟩
    rw [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply, star_star]
  have H2 : ∃ a ∈ M₁.map f, a ≠ 0 := by
    obtain ⟨x, hx⟩ : ∃ x, h z x ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hz0 (hd z hcon)
    obtain ⟨t, ht0, htx⟩ := hM₁.span x
    refine ⟨h (t • x) z, (hfA _).mpr ⟨_, htx, rfl⟩, ?_⟩
    have e := hs.eq z x
    rw [starRingEnd_apply] at e
    rw [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, ← e, starRingEnd_apply]
    exact mul_ne_zero (star_ne_zero.mpr ht0) (star_ne_zero.mpr hx)
  have H3 : ∃ t : K, t ≠ 0 ∧ ∀ a ∈ M₁.map f, t * a ∈ locRing p := by
    refine ⟨1, one_ne_zero, fun a ha => ?_⟩
    obtain ⟨m, hm, rfl⟩ := (hfA a).mp ha
    rw [one_mul]
    exact hM₁.int _ hm _ hz₁
  obtain ⟨α, hαA, hα0, hdiv⟩ := hS.principal (M₁.map f) H1 H2 H3
  obtain ⟨m₀, hm₀, rfl⟩ := (hfA α).mp hαA
  have hinv : (h m₀ z)⁻¹ ∈ locRing p := by
    apply hp₁
    apply hM₁.dual
    intro m hm
    rw [map_smul, smul_eq_mul, mul_comm]
    exact hdiv _ ((hfA _).mpr ⟨m, hm, rfl⟩)
  refine ⟨(star (h m₀ z))⁻¹ • m₀, hM₁.smul_mem _ ?_ _ hm₀, ?_⟩
  · rw [← star_inv₀]
    exact hS.star_mem _ hinv
  · have e := hs.eq m₀ z
    rw [starRingEnd_apply] at e
    rw [map_smul, smul_eq_mul, ← e]
    exact inv_mul_cancel₀ (star_ne_zero.mpr hα0)
end Formalism.L2.SG.Pf.LatDictZ.Z3
