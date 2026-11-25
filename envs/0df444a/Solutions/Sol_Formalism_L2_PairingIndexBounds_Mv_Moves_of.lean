-- Prove2me | solution 1 for Formalism.L2.PairingIndexBounds.Mv.Moves_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:09:48.629666+00:00
-- url     : https://prove2.me/submissions/8f271cd2-cb48-4a0a-a8d2-867f7fc6a912

import Definitions.Def_Formalism_LocalToGlobal_PairingIndexBounds_ModelLatticeMoves_ModelMoves
import Definitions.Def_Formalism_LocalToGlobal_PairingIndexBounds_ModelLatticeMoves_ModelIndexPairings_FourierTransformIdentityHolds
import Theorems.Thm_Formalism_L2_PairingIndexBounds_Mv_lattice_moves_hold

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
theorem _root_.solution (_h1 : ModelMoves) (_h3 : XiInter) : Moves := lattice_moves_hold
end Formalism.L2.PairingIndexBounds.Mv
