-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.PinE.eq_block_of_fix
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:33:54.249134+00:00
-- url     : https://prove2.me/submissions/08d1e375-3472-4aaa-8ce3-e01d34b484e0

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensitySixth
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_EqBlockOfFix
import Theorems.Thm_Formalism_H_dualEquiv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply



set_option autoImplicit false
open Matrix
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.PinE
variable {A : Type*} [CommRing A] [StarRing A] {κ : Type} [Fintype κ] [DecidableEq κ]
namespace Formalism.HermitianLattices.Ext.L3.PinE
theorem _root_.solution {H' : Matrix κ κ A} {Y : Matrix (Unit ⊕ κ) (Unit ⊕ κ) A}
    (hY : Yᴴ * HH H' * Y = HH H') (h0 : Y *ᵥ e₀ = e₀) :
    Y.toBlocks₂₂ᴴ * H' * Y.toBlocks₂₂ = H' ∧ Y = fromBlocks 1 0 0 Y.toBlocks₂₂ := by
  have h11 : Y (Sum.inl ()) (Sum.inl ()) = 1 := by
    have := congrFun h0 (Sum.inl ())
    simpa [e₀, mulVec_single_one] using this
  have h21 : ∀ i, Y (Sum.inr i) (Sum.inl ()) = 0 := by
    intro i
    have := congrFun h0 (Sum.inr i)
    simpa [e₀, mulVec_single_one] using this
  have hA : Y.toBlocks₁₁ = 1 := by
    ext ⟨⟩ ⟨⟩
    simpa [toBlocks₁₁] using h11
  have hC : Y.toBlocks₂₁ = 0 := by
    ext i ⟨⟩
    simpa [toBlocks₂₁] using h21 i
  have hYb : Y = fromBlocks 1 Y.toBlocks₁₂ 0 Y.toBlocks₂₂ := by
    conv_lhs => rw [← fromBlocks_toBlocks Y]
    rw [hA, hC]
  rw [hYb] at hY
  have key := congrArg Matrix.toBlocks₁₂ hY
  have key2 := congrArg Matrix.toBlocks₂₂ hY
  simp [HH, fromBlocks_conjTranspose, fromBlocks_multiply] at key key2
  refine ⟨?_, ?_⟩
  · simpa [key] using key2
  · rw [key] at hYb
    exact hYb
end Formalism.HermitianLattices.Ext.L3.PinE
