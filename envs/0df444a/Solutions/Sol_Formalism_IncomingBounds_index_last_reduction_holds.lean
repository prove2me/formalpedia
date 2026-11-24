-- Prove2me | solution 1 for Formalism.IncomingBounds.index_last_reduction_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:05:28.687204+00:00
-- url     : https://prove2.me/submissions/4838a554-0c3e-4679-ad71-f0fc22cd694e

import Definitions.Def_Formalism_IncomingBounds_IndexLastStep
import Definitions.Def_Formalism_LogFactorialIndices_SignedSubspaceIndex_SubspaceLatticeIndexSigned
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_IndexLastReductionHolds
import Theorems.Thm_Formalism_IncomingBounds_LatticeIndexAlt_idx_comap
import Theorems.Thm_Formalism_IncomingBounds_LatticeIndexAlt_isLat_scale
import Theorems.Thm_Formalism_IncomingBounds_LatticeIndexAlt_isLat_sup
import Theorems.Thm_Formalism_LatticeIndexTer_LatticeIndexValuation_isLat_comap
import Theorems.Thm_Formalism_LatticeIndexTer_LatticeIndexValuation_length_map_inj
import Theorems.Thm_Formalism_LatticeIndexTer_lattice_index_add
import Theorems.Thm_Formalism_LatticeIndexTer_lattice_index_scale
import Theorems.Thm_Formalism_LatticeIndexTer_lattice_quotient_finite
import Theorems.Thm_Formalism_LatticeIndexTer_subgroupData_length_le_of_le
import Theorems.Thm_Formalism_LatticeIndexTer_subgroupData_qlen_eq_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Module
open scoped Pointwise
open Formalism Formalism.IncomingBounds
open Formalism.LatticeIndexTer LatticeIndexAlt
namespace Formalism.IncomingBounds
theorem _root_.solution : IndexLastStep := by
  intro O K X _ _ _ _ _ _ _ _ _ _ _ ϖ hϖ e M Θ hM hΘ W
  rw [← idx_comap W M Θ]
  have hc : (algebraMap O K ϖ) ^ e ≠ 0 :=
    zpow_ne_zero _ ((map_ne_zero_iff _ (IsFractionRing.injective O K)).2 hϖ.ne_zero)
  have hNl := isLat_sup (K := K)
    (M.map ((((algebraMap O K ϖ) ^ e) • LinearMap.id : X →ₗ[K] X).restrictScalars O)) Θ
    (hM.1.map _) hΘ
  generalize hN : M.map ((((algebraMap O K ϖ) ^ e) • LinearMap.id : X →ₗ[K] X).restrictScalars O)
    ⊔ Θ = N at hNl ⊢
  have hMN : ∀ x ∈ M, (algebraMap O K ϖ) ^ e • x ∈ N := by
    intro x hx
    rw [← hN]
    exact Submodule.mem_sup_left ⟨x, hx, by simp⟩
  have hΘN : Θ ≤ N := hN ▸ le_sup_right
  let ι : W →ₗ[O] X := (W.subtype).restrictScalars O
  have hι : Function.Injective ι := Subtype.val_injective
  let fW : W →ₗ[O] W := ((((algebraMap O K ϖ) ^ e) • LinearMap.id : W →ₗ[K] W).restrictScalars O)
  have hA₀ : IsLat O K W (M.comap ι) := LatticeIndexValuation.isLat_comap M hM W
  have hB₀ : IsLat O K W (Θ.comap ι) := LatticeIndexValuation.isLat_comap Θ hΘ W
  have hN₀ : IsLat O K W (N.comap ι) := LatticeIndexValuation.isLat_comap N hNl W
  have hS₀ : IsLat O K W ((M.comap ι).map fW) := isLat_scale _ hc _ hA₀
  have hadd1 := lattice_index_add O K W (M.comap ι) ((M.comap ι).map fW) (Θ.comap ι) hA₀ hS₀ hB₀
  have hadd2 := lattice_index_add O K W ((M.comap ι).map fW) (N.comap ι) (Θ.comap ι) hS₀ hN₀ hB₀
  have h1 : idx O W (M.comap ι) ((M.comap ι).map fW) = e * (finrank K W : ℤ) := by
    have hs := lattice_index_scale O K W ϖ hϖ (-e) (M.comap ι) hA₀
    rw [neg_neg] at hs
    exact hs
  have hSN : (M.comap ι).map fW ≤ N.comap ι := by
    rintro _ ⟨y, hy, rfl⟩
    have := hMN _ hy
    simpa [ι, fW] using this
  have h2 : idx O W ((M.comap ι).map fW) (N.comap ι) ≤ 0 := by
    unfold idx
    rw [subgroupData.qlen_eq_zero hSN]
    simp
  have hle : qlen O W (N.comap ι) (Θ.comap ι) ≤ qlen O X N Θ := by
    unfold qlen
    rw [LatticeIndexValuation.length_map_inj ι hι]
    refine subgroupData.length_le_of_le (Submodule.map_comap_le ι N) (Submodule.map_comap_le ι Θ) ?_
    intro x hx
    obtain ⟨⟨w, -, rfl⟩, hxΘ⟩ := Submodule.mem_inf.mp hx
    exact ⟨w, hxΘ, rfl⟩
  have h3 : idx O W (N.comap ι) (Θ.comap ι) ≤ ((qlen O X N Θ).toNat : ℤ) := by
    have h4 : (qlen O W (N.comap ι) (Θ.comap ι)).toNat ≤ (qlen O X N Θ).toNat :=
      ENat.toNat_le_toNat hle (lattice_quotient_finite O K X N Θ hNl hΘ)
    unfold idx
    omega
  linarith
end Formalism.IncomingBounds
