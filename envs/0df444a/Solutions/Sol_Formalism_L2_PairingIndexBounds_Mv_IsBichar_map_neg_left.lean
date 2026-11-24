-- Prove2me | solution 1 for Formalism.L2.PairingIndexBounds.Mv.IsBichar.map_neg_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:14:15.487839+00:00
-- url     : https://prove2.me/submissions/507287db-76a4-44d7-a1a1-08c0483bbf70

import Definitions.Def_Formalism_LocalToGlobal_PairingIndexBounds_ModelLatticeMoves_ModelMoves
import Definitions.Def_Formalism_LocalToGlobal_PairingIndexBounds_ModelLatticeMoves_ModelIndexPairings_FourierTransformIdentityHolds
import Theorems.Thm_Formalism_L2_PairingIndexBounds_Mv_IsBichar_map_zero_left

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
variable {c : B → A → k}
namespace Formalism.L2.PairingIndexBounds.Mv
namespace IsBichar
theorem _root_.solution (hc : IsBichar c) (b : B) (a : A) : c (-b) a = (c b a)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← hc.2.1, neg_add_cancel, hc.map_zero_left]
end IsBichar
end Formalism.L2.PairingIndexBounds.Mv
