-- Prove2me | solution 1 for Formalism.L2.PairingIndexBounds.Mv.IsBichar.map_sub_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:21:19.475841+00:00
-- url     : https://prove2.me/submissions/1382ec81-eb9e-4114-9142-4950834ddf6a

import Definitions.Def_Formalism_LocalToGlobal_PairingIndexBounds_ModelLatticeMoves_ModelMoves
import Definitions.Def_Formalism_LocalToGlobal_PairingIndexBounds_ModelLatticeMoves_ModelIndexPairings_FourierTransformIdentityHolds
import Theorems.Thm_Formalism_L2_PairingIndexBounds_Mv_IsBichar_map_neg_left

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
theorem _root_.solution (hc : IsBichar c) (b b' : B) (a : A) : c (b - b') a = c b a * (c b' a)⁻¹ := by
  rw [sub_eq_add_neg, hc.2.1, hc.map_neg_left]
end IsBichar
end Formalism.L2.PairingIndexBounds.Mv
