-- Prove2me | solution 1 for Formalism.L2.PairingIndexBounds.Mv.gen_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:46:57.672623+00:00
-- url     : https://prove2.me/submissions/a6c5059b-2a43-4957-bbfc-a96021397938

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
theorem _root_.solution (c : B → A → k) (A₀ : AddSubgroup A) (a : A) (b : B) (t : A) :
    gen c A₀ a b t = c b (t + a) * ind (A₀ : Set A) (t + a) := rfl
end Formalism.L2.PairingIndexBounds.Mv
