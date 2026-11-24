-- Prove2me | solution 1 for Formalism.L2.PairingIndexBounds.Mv.IsXi.fixed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:20:22.215005+00:00
-- url     : https://prove2.me/submissions/e094e63b-cc5e-4afe-8625-f16a5f363ec9

import Definitions.Def_Formalism_LocalToGlobal_PairingIndexBounds_ModelLatticeMoves_ModelMoves
import Definitions.Def_Formalism_LocalToGlobal_PairingIndexBounds_ModelLatticeMoves_ModelIndexPairings_FourierTransformIdentityHolds
import Theorems.Thm_Formalism_L2_PairingIndexBounds_Mv_IsBichar_map_zero_left
import Theorems.Thm_Formalism_L2_PairingIndexBounds_Mv_ind_of_mem
import Theorems.Thm_Formalism_L2_PairingIndexBounds_Mv_ind_of_not_mem
import Theorems.Thm_Formalism_L2_PairingIndexBounds_Mv_gen_apply
import Theorems.Thm_Formalism_L2_PairingIndexBounds_Mv_IsHeis_WA_zero
import Theorems.Thm_Formalism_L2_PairingIndexBounds_Mv_IsHeis_WB_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.L2 Formalism.L2.PairingIndexBounds Formalism.L2.PairingIndexBounds.Mv
variable {k : Type*} [Field k] {A B T : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup T] [Module k T]
namespace Formalism.L2.PairingIndexBounds.Mv
namespace IsXi
theorem _root_.solution {c : B → A → k} {WA : A → T →ₗ[k] T} {WB : B → T →ₗ[k] T} {A₀ : AddSubgroup A} {θ : T}
    {Xi : Sch c A₀ →ₗ[k] T} (hXi : IsXi c WA WB A₀ θ Xi) (hc : IsBichar c) (hW : IsHeis c WA WB) (a : A)
    (ha : a ∈ A₀) : WA a θ = θ := by
  have e : gen c A₀ a 0 = gen c A₀ 0 0 := by
    funext t
    rw [gen_apply, gen_apply, hc.map_zero_left, hc.map_zero_left, add_zero]
    by_cases ht : t ∈ A₀
    · rw [ind_of_mem (show t ∈ (A₀ : Set A) from ht), ind_of_mem (show t + a ∈ (A₀ : Set A) from A₀.add_mem ht ha)]
    · have : t + a ∉ (A₀ : Set A) := by
        intro h
        apply ht
        have := A₀.sub_mem h ha
        rwa [add_sub_cancel_right] at this
      rw [ind_of_not_mem (show t ∉ (A₀ : Set A) from ht), ind_of_not_mem this]
  have h1 := hXi a 0
  have h2 := hXi 0 0
  have e' : (⟨gen c A₀ a 0, gen_mem c A₀ a 0⟩ : Sch c A₀) = ⟨gen c A₀ 0 0, gen_mem c A₀ 0 0⟩ := Subtype.ext e
  rw [e', h2, hW.WB_zero, hW.WA_zero] at h1
  exact h1.symm
end IsXi
end Formalism.L2.PairingIndexBounds.Mv
