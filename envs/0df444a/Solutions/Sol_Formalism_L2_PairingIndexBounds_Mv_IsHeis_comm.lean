-- Prove2me | solution 1 for Formalism.L2.PairingIndexBounds.Mv.IsHeis.comm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:47:00.488585+00:00
-- url     : https://prove2.me/submissions/b0411014-fa0b-4d9e-8632-1901140fea85

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
theorem _root_.solution (hW : IsHeis c WA WB) (a : A) (b : B) (x : T) : WA a (WB b x) = c b a • WB b (WA a x) :=
  LinearMap.congr_fun (hW.2.2.2.2 a b) x
end IsHeis
end Formalism.L2.PairingIndexBounds.Mv
