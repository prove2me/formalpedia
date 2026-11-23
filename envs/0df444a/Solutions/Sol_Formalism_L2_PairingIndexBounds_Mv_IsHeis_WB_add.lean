-- Prove2me | solution 1 for Formalism.L2.PairingIndexBounds.Mv.IsHeis.WB_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:18:28.022735+00:00
-- url     : https://prove2.me/submissions/24e94355-f279-48cf-9ce6-6d74867aea14

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
theorem _root_.solution (hW : IsHeis c WA WB) (b b' : B) (x : T) : WB (b + b') x = WB b (WB b' x) := by
  rw [hW.2.2.2.1]; rfl
end IsHeis
end Formalism.L2.PairingIndexBounds.Mv
