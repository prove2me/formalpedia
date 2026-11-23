-- Prove2me | solution 1 for Formalism.L2.PairingIndexBounds.Mv.eFam_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:18:30.124926+00:00
-- url     : https://prove2.me/submissions/597fe9d5-f13a-475e-9536-0b587f23472f

import Definitions.Def_Formalism_LocalToGlobal_PairingIndexBounds_ModelLatticeMoves_ModelMoves
import Definitions.Def_Formalism_LocalToGlobal_PairingIndexBounds_ModelLatticeMoves_ModelIndexPairings_FourierTransformIdentityHolds

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
theorem _root_.solution (A₀ : AddSubgroup A) (i : (A ⧸ A₀) × (Multiplicative A₀ →* k)) (t : A) (h : t + i.1.out ∈ A₀) :
    eFam A₀ i t = i.2 (Multiplicative.ofAdd ⟨t + i.1.out, h⟩) := by
  unfold eFam; exact dif_pos h
end Formalism.L2.PairingIndexBounds.Mv
