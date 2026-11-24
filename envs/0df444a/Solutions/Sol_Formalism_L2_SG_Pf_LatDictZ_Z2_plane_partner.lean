-- Prove2me | solution 1 for Formalism.L2.SG.Pf.LatDictZ.Z2.plane_partner
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:05:12.752594+00:00
-- url     : https://prove2.me/submissions/b6264546-2c17-4ebf-b18a-1428c2ea4ea1

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_LatDictZAbs
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_LatDictZPlane
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
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
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.LatDictZ Formalism.L2.SG.Pf.LatDictZ.Z2
open ReciprocityTheory.ChartRestriction.L3.WA
variable {K : Type} [Field K] [StarRing K] {V : Type} [AddCommGroup V] [Module K V]
namespace Formalism.L2.SG.Pf.LatDictZ.Z2
theorem _root_.solution {S : Subring K} (hS : IsHermSemilocal S) (B : V →ₗ⋆[K] V →ₗ[K] K)
    (hsym : ∀ x y, star (B x y) = B y x) {N : AddSubgroup V} (hsm : ∀ a ∈ S, ∀ m ∈ N, a • m ∈ N)
    (hint : ∀ x ∈ N, ∀ y ∈ N, B x y ∈ S) (hdual : ∀ x, (∀ m ∈ N, B m x ∈ S) → x ∈ N) {v : V}
    (hv : v ∈ N) (hprim : ∀ c : K, c • v ∈ N → c ∈ S) {m0 : V} (hm0 : m0 ∈ N) (hne : B v m0 ≠ 0) :
    ∃ m ∈ N, B v m = 1 := by
  let A : AddSubgroup K :=
    { carrier := {a | ∃ m ∈ N, B v m = a}
      zero_mem' := ⟨0, N.zero_mem, by simp⟩
      add_mem' := by
        rintro _ _ ⟨m, hm, rfl⟩ ⟨m', hm', rfl⟩
        exact ⟨m + m', N.add_mem hm hm', by simp⟩
      neg_mem' := by
        rintro _ ⟨m, hm, rfl⟩
        exact ⟨-m, N.neg_mem hm, by simp⟩ }
  have hA : ∀ s ∈ S, ∀ a ∈ A, s * a ∈ A := by
    rintro s hs _ ⟨m, hm, rfl⟩
    exact ⟨s • m, hsm s hs m hm, by simp⟩
  have hA0 : ∃ a ∈ A, a ≠ 0 := ⟨B v m0, ⟨m0, hm0, rfl⟩, hne⟩
  have hAb : ∃ t : K, t ≠ 0 ∧ ∀ a ∈ A, t * a ∈ S := by
    refine ⟨1, one_ne_zero, ?_⟩
    rintro _ ⟨m, hm, rfl⟩
    simpa using hint v hv m hm
  obtain ⟨β, hβA, hβ0, hdiv⟩ := hS.principal A hA hA0 hAb
  obtain ⟨m1, hm1, hβ⟩ := hβA
  have hx : (star β)⁻¹ • v ∈ N := by
    apply hdual
    intro m hm
    have h1 := hdiv (B v m) ⟨m, hm, rfl⟩
    have e : B m ((star β)⁻¹ • v) = star (B v m * β⁻¹) := by
      rw [map_smul, smul_eq_mul, ← hsym v m, star_mul', star_inv₀]
      ring
    rw [e]
    exact hS.star_mem _ h1
  have hc := hprim _ hx
  have hβi : β⁻¹ ∈ S := by
    have := hS.star_mem _ hc
    rwa [star_inv₀, star_star] at this
  refine ⟨β⁻¹ • m1, hsm _ hβi _ hm1, ?_⟩
  rw [map_smul, smul_eq_mul, hβ, inv_mul_cancel₀ hβ0]
end Formalism.L2.SG.Pf.LatDictZ.Z2
