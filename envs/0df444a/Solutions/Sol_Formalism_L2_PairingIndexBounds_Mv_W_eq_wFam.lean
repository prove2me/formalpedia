-- Prove2me | solution 1 for Formalism.L2.PairingIndexBounds.Mv.W_eq_wFam
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:30:45.145077+00:00
-- url     : https://prove2.me/submissions/e273cf6f-0612-45de-a56c-bda4baf950dd

import Definitions.Def_Formalism_LocalToGlobal_PairingIndexBounds_ModelLatticeMoves_ModelMoves
import Definitions.Def_Formalism_LocalToGlobal_PairingIndexBounds_ModelLatticeMoves_ModelIndexPairings_FourierTransformIdentityHolds
import Theorems.Thm_Formalism_L2_PairingIndexBounds_Mv_IsBichar_map_sub_left
import Theorems.Thm_Formalism_L2_PairingIndexBounds_Mv_IsHeis_WA_add
import Theorems.Thm_Formalism_L2_PairingIndexBounds_Mv_IsHeis_WB_add
import Theorems.Thm_Formalism_L2_PairingIndexBounds_Mv_IsHeis_comm
import Theorems.Thm_Formalism_L2_PairingIndexBounds_Mv_chi_apply
import Theorems.Thm_Formalism_L2_PairingIndexBounds_Mv_out_sub_mem

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
theorem _root_.solution (c : B → A → k) (hc : IsBichar c) (WA : A → T →ₗ[k] T) (WB : B → T →ₗ[k] T) (hW : IsHeis c WA WB)
    (A₀ : AddSubgroup A) (θ : T) (hA : ∀ a ∈ A₀, WA a θ = θ) (hB : ∀ b, (∀ a ∈ A₀, c b a = 1) → WB b θ = θ)
    (a : A) (b : B) :
    WA a (WB b θ) = c b (a - (QuotientAddGroup.mk a : A ⧸ A₀).out) •
      wFam c hc WA WB A₀ θ ((QuotientAddGroup.mk a : A ⧸ A₀), chi c hc A₀ b) := by
  have h0 := out_sub_mem A₀ a
  have hex : ∃ b', chi c hc A₀ b' = chi c hc A₀ b := ⟨b, rfl⟩
  have hw : wFam c hc WA WB A₀ θ ((QuotientAddGroup.mk a : A ⧸ A₀), chi c hc A₀ b)
      = WA (QuotientAddGroup.mk a : A ⧸ A₀).out (WB hex.choose θ) := by
    unfold wFam; exact dif_pos hex
  have hb' : ∀ s ∈ A₀, c hex.choose s = c b s := by
    intro s hs
    have := DFunLike.congr_fun hex.choose_spec (Multiplicative.ofAdd (⟨s, hs⟩ : A₀))
    rwa [chi_apply, chi_apply] at this
  have hθ : WB b θ = WB hex.choose θ := by
    have e : b = hex.choose + (b - hex.choose) := by abel
    conv_lhs => rw [e, hW.WB_add]
    rw [hB (b - hex.choose)]
    intro s hs
    rw [hc.map_sub_left, hb' s hs, mul_inv_cancel₀ (hc.1 b s)]
  rw [hw, hθ]
  have e : a = (QuotientAddGroup.mk a : A ⧸ A₀).out + (a - (QuotientAddGroup.mk a : A ⧸ A₀).out) := by abel
  conv_lhs => rw [e, hW.WA_add, hW.comm, hA _ h0, map_smul, hb' _ h0]
end Formalism.L2.PairingIndexBounds.Mv
