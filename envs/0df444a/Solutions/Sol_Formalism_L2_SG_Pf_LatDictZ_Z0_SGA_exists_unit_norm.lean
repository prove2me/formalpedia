-- Prove2me | solution 1 for Formalism.L2.SG.Pf.LatDictZ.Z0.SGA.exists_unit_norm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:20:21.459066+00:00
-- url     : https://prove2.me/submissions/efcc7291-c55a-47e1-a72e-524b29f74612

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_LatDictZAbs
import Definitions.Def_Formalism_SelfDualUnimodular_LocalLatticeDictionary_ExistsUnitNorm
import Theorems.Thm_Formalism_L2_SG_Pf_LatDictZ_Z0_SGA_inJ_of_fixed
import Theorems.Thm_Formalism_L2_SG_Pf_LatDictZ_Z0_SGA_InJ_add
import Theorems.Thm_Formalism_L2_SG_Pf_LatDictZ_Z0_SGA_InJ_mul
import Theorems.Thm_Formalism_L2_SG_Pf_LatDictZ_Z0_SGA_InJ_one_add
import Theorems.Thm_Formalism_L2_SG_Pf_LatDictZ_Z0_SGA_norm_add_smul
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L3_WA_exists_trace_eq
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
    {M : AddSubgroup V} (hM : IsSelfDualMod (locRing p) h M) (x₀ : V) (hx₀ : x₀ ≠ 0) :
    ∃ e ∈ M, IsUnitIn (locRing p) (h e e) := by
  have hS := isHermSemilocal_locRing hK hp
  set S := locRing p with hSdef
  have hsym : ∀ u v, star (h u v) = h v u := fun u v => hs.eq u v
  obtain ⟨m, htM, hm0⟩ : ∃ m ∈ M, m ≠ 0 := by
    obtain ⟨t, ht0, htM⟩ := hM.span x₀
    exact ⟨t • x₀, htM, smul_ne_zero ht0 hx₀⟩
  obtain ⟨y, hy⟩ : ∃ y, h m y ≠ 0 := by
    by_contra hc; push Not at hc; exact hm0 (hnd m hc)
  obtain ⟨t', ht'0, ht'M⟩ := hM.span y
  let f : V →+ K :=
    { toFun := fun u => h u m
      map_zero' := by simp
      map_add' := by intro a b; simp }
  have hf : ∀ u, f u = h u m := fun _ => rfl
  have hAS : ∀ c ∈ S, ∀ a ∈ M.map f, c * a ∈ M.map f := by
    rintro c hc _ ⟨u, hu, rfl⟩
    refine ⟨star c • u, hM.smul_mem _ (hS.star_mem _ hc) _ hu, ?_⟩
    rw [hf, hf, map_smulₛₗ, LinearMap.smul_apply, starRingEnd_apply, star_star, smul_eq_mul]
  have h0 : ∃ a ∈ M.map f, a ≠ 0 := by
    refine ⟨_, ⟨t' • y, ht'M, rfl⟩, ?_⟩
    rw [hf, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply, ← hsym m y]
    exact mul_ne_zero (star_ne_zero.mpr ht'0) (star_ne_zero.mpr hy)
  have hb : ∀ a ∈ M.map f, (1 : K) * a ∈ S := by
    rintro _ ⟨u, hu, rfl⟩
    rw [one_mul]; exact hM.int u hu m htM
  obtain ⟨α, ⟨w₀, hw₀, hα⟩, hα0, hdiv⟩ := hS.principal (M.map f) hAS h0 ⟨1, one_ne_zero, hb⟩
  rw [hf] at hα
  have hyM : α⁻¹ • m ∈ M := by
    apply hM.dual
    intro u hu
    have := hdiv _ ⟨u, hu, rfl⟩
    rw [map_smul, smul_eq_mul, mul_comm]
    exact this
  have hxy : h w₀ (α⁻¹ • m) = 1 := by
    rw [map_smul, smul_eq_mul, hα, inv_mul_cancel₀ hα0]
  have hyx : h (α⁻¹ • m) w₀ = 1 := by rw [← hsym, hxy, star_one]
  generalize α⁻¹ • m = y' at hyM hxy hyx
  by_cases hux : IsUnitIn S (h w₀ w₀)
  · exact ⟨w₀, hw₀, hux⟩
  by_cases huy : IsUnitIn S (h y' y')
  · exact ⟨y', hyM, huy⟩
  obtain ⟨κ, hκ, hκt⟩ := exists_trace_eq hS S.one_mem (star_one K)
  refine ⟨w₀ + κ • y', M.add_mem hw₀ (hM.smul_mem _ hκ _ hyM), ?_⟩
  have hJx := inJ_of_fixed hp.isPrime (hM.int _ hw₀ _ hw₀) (hsym w₀ w₀) hux
  have hJy := inJ_of_fixed hp.isPrime (hM.int _ hyM _ hyM) (hsym _ _) huy
  have e : h (w₀ + κ • y') (w₀ + κ • y') = 1 + (h w₀ w₀ + (star κ * κ) * h y' y') := by
    rw [norm_add_smul, hxy, hyx]
    linear_combination hκt
  rw [e]
  exact (hJx.add hp.isPrime (hJy.mul hp.isPrime (S.mul_mem (hS.star_mem _ hκ) hκ))).one_add hp.isPrime
end Formalism.L2.SG.Pf.LatDictZ.Z0.SGA
