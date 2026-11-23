-- Prove2me | solution 1 for Formalism.L2.PairingIndexBounds.Mv.rhoA_gen
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:21:50.787102+00:00
-- url     : https://prove2.me/submissions/43971c6e-2569-4173-be75-2c4e9fa138a7

import Definitions.Def_Formalism_LocalToGlobal_PairingIndexBounds_ModelLatticeMoves_ModelMoves
import Definitions.Def_Formalism_LocalToGlobal_PairingIndexBounds_ModelLatticeMoves_ModelIndexPairings_FourierTransformIdentityHolds
import Theorems.Thm_Formalism_L2_PairingIndexBounds_Mv_gen_apply

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
theorem _root_.solution (c : B → A → k) (A₀ : AddSubgroup A) (a' a : A) (b : B) :
    rhoA a' (gen c A₀ a b) = gen c A₀ (a' + a) b := by
  funext t
  change gen c A₀ a b (t + a') = _
  rw [gen_apply, gen_apply, add_assoc]
end Formalism.L2.PairingIndexBounds.Mv
