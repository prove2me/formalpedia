-- Prove2me | solution 1 for Formalism.L2.PairingIndexBounds.Mv.rhoB_gen
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:18:31.561619+00:00
-- url     : https://prove2.me/submissions/5ec3b448-827f-4991-ab0a-437d9a6b830d

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
theorem _root_.solution (c : B → A → k) (hc : IsBichar c) (A₀ : AddSubgroup A) (b' : B) (a : A) (b : B) :
    rhoB c b' (gen c A₀ a b) = (c b' a)⁻¹ • gen c A₀ a (b' + b) := by
  funext t
  change c b' t * gen c A₀ a b t = (c b' a)⁻¹ * gen c A₀ a (b' + b) t
  rw [gen_apply, gen_apply, hc.2.1, hc.2.2 b' t a]
  have h := hc.1 b' a
  field_simp
end Formalism.L2.PairingIndexBounds.Mv
