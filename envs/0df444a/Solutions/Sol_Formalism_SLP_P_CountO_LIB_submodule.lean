-- Prove2me | solution 1 for Formalism.SLP.P.CountO.LIB.submodule
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:17:35.464146+00:00
-- url     : https://prove2.me/submissions/e654ae60-63c0-4005-a5b6-95fc9e902306

import Definitions.Def_Formalism_HyperbolicPlaceProducts_Statement
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SubgroupIndexCounts_CountO

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
noncomputable section
open Formalism Formalism.SLP Formalism.SLP.P
open Formalism.SLP.P.CountO
open NumberField
variable (E : Type) [Field E] [NumberField E]
variable {E}
namespace Formalism.SLP.P.CountO
namespace LIB
theorem _root_.solution {X : Type} [AddCommGroup X] [Module (𝓞 E) X] {k : ℕ} (h : LIB E X k)
    (L : Submodule (𝓞 E) X) : LIB E L k := by
  intro ι _ v hv
  exact h ι (L.subtype ∘ v) (hv.map' L.subtype (Submodule.ker_subtype L))
end LIB
end Formalism.SLP.P.CountO
