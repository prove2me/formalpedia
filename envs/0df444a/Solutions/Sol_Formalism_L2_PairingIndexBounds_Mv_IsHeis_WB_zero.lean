-- Prove2me | solution 1 for Formalism.L2.PairingIndexBounds.Mv.IsHeis.WB_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:13:53.820898+00:00
-- url     : https://prove2.me/submissions/14b23b24-bdd3-475b-b768-6ba1d317b192

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
variable {c : B → A → k} {WA : A → T →ₗ[k] T} {WB : B → T →ₗ[k] T}
namespace Formalism.L2.PairingIndexBounds.Mv
namespace IsHeis
theorem _root_.solution (hW : IsHeis c WA WB) (x : T) : WB 0 x = x := by rw [hW.2.2.1]; rfl
end IsHeis
end Formalism.L2.PairingIndexBounds.Mv
