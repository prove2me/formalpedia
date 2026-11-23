-- Prove2me | solution 1 for Formalism.L2.PairingIndexBounds.Mv.out_sub_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:18:31.56915+00:00
-- url     : https://prove2.me/submissions/295f9bca-67ba-4374-a060-9eb26b43f1ed

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
theorem _root_.solution (A₀ : AddSubgroup A) (a : A) : a - (QuotientAddGroup.mk a : A ⧸ A₀).out ∈ A₀ := by
  obtain ⟨h, hh⟩ := QuotientAddGroup.mk_out_eq_add A₀ a
  rw [hh]
  have e : a - (a + (h : A)) = -(h : A) := by abel
  rw [e]
  exact A₀.neg_mem h.2
end Formalism.L2.PairingIndexBounds.Mv
