-- Prove2me | solution 1 for Formalism.L2.PairingIndexBounds.Mv.IsHeis.WA_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:16:59.769257+00:00
-- url     : https://prove2.me/submissions/b256763e-9667-4f5b-8c5e-0b1d1f30a4c2

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
theorem _root_.solution (hW : IsHeis c WA WB) (a a' : A) (x : T) : WA (a + a') x = WA a (WA a' x) := by
  rw [hW.2.1]; rfl
end IsHeis
end Formalism.L2.PairingIndexBounds.Mv
