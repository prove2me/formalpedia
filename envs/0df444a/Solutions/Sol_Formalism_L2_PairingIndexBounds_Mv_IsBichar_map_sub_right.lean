-- Prove2me | solution 1 for Formalism.L2.PairingIndexBounds.Mv.IsBichar.map_sub_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:09:43.926188+00:00
-- url     : https://prove2.me/submissions/0c377c64-adcb-403a-820b-d19ca2426551

import Definitions.Def_Formalism_LocalToGlobal_PairingIndexBounds_ModelLatticeMoves_ModelMoves
import Definitions.Def_Formalism_LocalToGlobal_PairingIndexBounds_ModelLatticeMoves_ModelIndexPairings_FourierTransformIdentityHolds
import Theorems.Thm_Formalism_L2_PairingIndexBounds_Mv_IsBichar_map_neg_right

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
theorem _root_.solution (hc : IsBichar c) (b : B) (a a' : A) : c b (a - a') = c b a * (c b a')⁻¹ := by
  rw [sub_eq_add_neg, hc.2.2, hc.map_neg_right]
end IsBichar
end Formalism.L2.PairingIndexBounds.Mv
