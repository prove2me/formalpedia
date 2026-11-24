-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.PinE.form_col
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:33:54.334325+00:00
-- url     : https://prove2.me/submissions/981a6450-0901-4aa1-a6df-4d79b6853582

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
theorem _root_.solution {H X : Matrix (Unit ⊕ κ) (Unit ⊕ κ) A} (hX : Xᴴ * H * X = H)
    (h00 : H (Sum.inl ()) (Sum.inl ()) = 1) : star (X *ᵥ e₀) ⬝ᵥ (H *ᵥ (X *ᵥ e₀)) = 1 := by
  rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, hX]
  simp [e₀, mulVec_single_one, dotProduct, Fintype.sum_sum_type, h00]
end Formalism.HermitianLattices.Ext.L3.PinE
