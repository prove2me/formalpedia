-- Prove2me | solution 1 for Formalism.L2.SG.Pf.G4.exists_isom_map_of_eq_norm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:54:16.090504+00:00
-- url     : https://prove2.me/submissions/3a7205a5-7cd8-42f4-967b-d57e9e476f2b

import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_AdelicThetaPoissonSummation
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_ExistsIsomScale
import Theorems.Thm_P2M_Formalism_L2_SG_Pf_G4_exists_isom_move__2f2ae1670e38
import Theorems.Thm_P2M_Formalism_L2_SG_Pf_G4_exists_isom_scale__8cb81202c702

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
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.G4
open Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.U0 Formalism.HermitianLattices.Ext.L3.WA
variable {K V : Type*} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
variable {S : Subring K} {π : K} {h : V →ₗ⋆[K] V →ₗ[K] K}
namespace Formalism.L2.SG.Pf.G4
theorem _root_.solution (hs : h.IsSymm) (h2 : (2 : K) ≠ 0) {x y : V} (hxy : h x x = h y y)
    (hx0 : h x x ≠ 0) :
    ∃ τ ∈ Formalism.HermitianLatticesTheory.isom h, τ x = y ∧ (∀ v, h x v = 0 → h y v = 0 → τ v = v) ∧
      ∀ W : Submodule K V, x ∈ W → y ∈ W → ∀ v, v ∈ W ↔ τ v ∈ W := by
  by_cases hb : h x x - h y x = 0
  · have hxy' : h x x = h (-y) (-y) := by
      simp only [map_neg, LinearMap.neg_apply, neg_neg]
      exact hxy
    have hyx : h y x = h x x := by linear_combination -hb
    have hb' : h x x - h (-y) x ≠ 0 := by
      simp only [map_neg, LinearMap.neg_apply, sub_neg_eq_add]
      rw [hyx, ← two_mul]
      exact mul_ne_zero h2 hx0
    obtain ⟨τ, hτ, hτx, hτv, hτW⟩ := exists_isom_move' hs hxy' hb'
    have hy0 : h y y ≠ 0 := hxy ▸ hx0
    obtain ⟨ψ, hψ, hψy, hψv, hψW⟩ := exists_isom_scale' hs hy0 (b := -1)
      (by rw [star_neg, star_one]; norm_num)
    refine ⟨ψ * τ, mul_mem hψ hτ, ?_, ?_, ?_⟩
    · show ψ (τ x) = y
      rw [hτx, map_neg, hψy, neg_one_smul, neg_neg]
    · intro v hxv hyv
      show ψ (τ v) = v
      have hyv' : h (-y) v = 0 := by
        simp only [map_neg, LinearMap.neg_apply, hyv, neg_zero]
      rw [hτv v hxv hyv', hψv v hyv]
    · intro W hxW hyW v
      show v ∈ W ↔ ψ (τ v) ∈ W
      rw [hτW W hxW (W.neg_mem hyW) v]
      exact hψW W hyW (τ v)
  · exact exists_isom_move' hs hxy hb
end Formalism.L2.SG.Pf.G4
