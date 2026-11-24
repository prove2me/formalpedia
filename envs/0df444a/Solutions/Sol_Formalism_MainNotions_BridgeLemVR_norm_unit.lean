-- Prove2me | solution 1 for Formalism.MainNotions.BridgeLemVR.norm_unit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:35:57.27252+00:00
-- url     : https://prove2.me/submissions/9953b7f0-c33a-43dc-b93d-130d0aeec43a

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsMassConstOne
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MassLandA
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_BridgeLemVR
import Theorems.Thm_Formalism_MainNotions_BridgeLemVR_one_mem_locR
import Theorems.Thm_Formalism_MainNotions_BridgeLemVR_mul_mem_locR
import Theorems.Thm_Formalism_MainNotions_BridgeLemVR_star_mem_locR
import Theorems.Thm_Formalism_MainNotions_BridgeLemVR_mem_one_of_locR
import Theorems.Thm_Formalism_MainNotions_BridgeLemVR_exists_local
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_RankOne_loc_mul
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_SplitA_mul_mem_locR
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_SplitA_one_mem_locR
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_SplitA_star_mem_locR
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply



set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.BridgeLemVR
open NumberField Formalism.HermitianLatticesTheory Formalism.ThetaLiftIndependence Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.RankOne nonZeroDivisors
variable {K : Type} [Field K] [NumberField K] [StarRing K]
namespace Formalism.MainNotions.BridgeLemVR
theorem _root_.solution (h : K →ₗ⋆[K] K →ₗ[K] K) (h1 : h 1 1 ≠ 0) {M M' : Submodule (𝓞 K) K}
    (hM : M ∈ genus h (1 : Submodule (𝓞 K) K)) (hM' : M' ∈ genus h (1 : Submodule (𝓞 K) K)) {a : K}
    (he : M = Submodule.span (𝓞 K) {a} * M') :
    a * star a ∈ (1 : Submodule (𝓞 K) K) ∧ (a * star a)⁻¹ ∈ (1 : Submodule (𝓞 K) K) := by
  have key : ∀ p : Ideal (𝓞 K), p.IsMaximal →
      a * star a ∈ locR (K := K) p ∧ (a * star a)⁻¹ ∈ locR (K := K) p := by
    intro p hp
    obtain ⟨z, hz, hzM⟩ := exists_local h h1 hM hp
    obtain ⟨z', hz', hzM'⟩ := exists_local h h1 hM' hp
    have hl : loc (K := K) p M = Submodule.span (𝓞 K) {a} * loc (K := K) p M' := by
      rw [he, loc_mul hp]
    have hzin : z ∈ loc (K := K) p M := (hzM z).2 ⟨1, one_mem_locR p, (one_mul z).symm⟩
    rw [hl, Submodule.mem_span_singleton_mul] at hzin
    obtain ⟨m, hm, hmz⟩ := hzin
    obtain ⟨r, hr, rfl⟩ := (hzM' m).1 hm
    have haz : a * z' ∈ loc (K := K) p M := by
      rw [hl, Submodule.mem_span_singleton_mul]
      exact ⟨z', (hzM' z').2 ⟨1, one_mem_locR p, (one_mul z').symm⟩, rfl⟩
    obtain ⟨r', hr', hr'e⟩ := (hzM _).1 haz
    have hz1 : z * star z = 1 := by rw [mul_comm]; exact hz
    have hz1' : z' * star z' = 1 := by rw [mul_comm]; exact hz'
    have t1 := congrArg (fun t => t * star t) hr'e
    simp only [star_mul'] at t1
    have e1 : a * star a = r' * star r' := by
      linear_combination t1 - (a * star a) * hz1' + (r' * star r') * hz1
    have t2 := congrArg (fun t => t * star t) hmz
    simp only [star_mul'] at t2
    have e2 : a * star a * (r * star r) = 1 := by
      linear_combination t2 - (a * star a * r * star r) * hz1' + hz1
    refine ⟨e1 ▸ mul_mem_locR hr' (star_mem_locR hr'), ?_⟩
    rw [inv_eq_of_mul_eq_one_right e2]
    exact mul_mem_locR hr (star_mem_locR hr)
  exact ⟨mem_one_of_locR fun p hp => (key p hp).1, mem_one_of_locR fun p hp => (key p hp).2⟩
end Formalism.MainNotions.BridgeLemVR
