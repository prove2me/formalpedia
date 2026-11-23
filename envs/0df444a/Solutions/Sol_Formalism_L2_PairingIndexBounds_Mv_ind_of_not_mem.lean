-- Prove2me | solution 1 for Formalism.L2.PairingIndexBounds.Mv.ind_of_not_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:46:58.177379+00:00
-- url     : https://prove2.me/submissions/5ca708cf-7e0a-433f-8952-88b498d494e5

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
theorem _root_.solution {S : Set A} {t : A} (h : t ∉ S) : ind (k := k) S t = 0 := by
  unfold ind; exact if_neg h
end Formalism.L2.PairingIndexBounds.Mv
