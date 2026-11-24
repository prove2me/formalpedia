-- Prove2me | solution 1 for Formalism.L2.SG.Pf.LatDictZ.Z2.plane_prim
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:00:33.417944+00:00
-- url     : https://prove2.me/submissions/810113b2-69ac-48b8-a534-0a60bb2e0c68

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
    {N : AddSubgroup V} (hsm : ∀ a ∈ S, ∀ m ∈ N, a • m ∈ N) (hint : ∀ x ∈ N, ∀ y ∈ N, B x y ∈ S)
    {z w : V} (hz : z ∈ N) (hzw : B z w = 1) (hspan : ∃ t : K, t ≠ 0 ∧ t • w ∈ N) :
    ∃ α : K, α ≠ 0 ∧ α • w ∈ N ∧ ∀ c : K, c • (α • w) ∈ N → c ∈ S := by
  let A : AddSubgroup K :=
    { carrier := {c | c • w ∈ N}
      zero_mem' := by simp [N.zero_mem]
      add_mem' := by
        intro a b ha hb
        show (a + b) • w ∈ N
        rw [add_smul]
        exact N.add_mem ha hb
      neg_mem' := by
        intro a ha
        show (-a) • w ∈ N
        rw [neg_smul]
        exact N.neg_mem ha }
  have hA : ∀ s ∈ S, ∀ a ∈ A, s * a ∈ A := by
    intro s hs a ha
    show (s * a) • w ∈ N
    rw [mul_smul]
    exact hsm s hs _ ha
  obtain ⟨t, ht0, htw⟩ := hspan
  have hAb : ∃ t : K, t ≠ 0 ∧ ∀ a ∈ A, t * a ∈ S := by
    refine ⟨1, one_ne_zero, ?_⟩
    intro a ha
    have := hint z hz _ ha
    simpa [map_smul, hzw] using this
  obtain ⟨α, hαA, hα0, hdiv⟩ := hS.principal A hA ⟨t, htw, ht0⟩ hAb
  refine ⟨α, hα0, hαA, fun c hc => ?_⟩
  have h1 : c * α ∈ A := by
    show (c * α) • w ∈ N
    rwa [mul_smul]
  have := hdiv _ h1
  rwa [mul_assoc, mul_inv_cancel₀ hα0, mul_one] at this
end Formalism.L2.SG.Pf.LatDictZ.Z2
