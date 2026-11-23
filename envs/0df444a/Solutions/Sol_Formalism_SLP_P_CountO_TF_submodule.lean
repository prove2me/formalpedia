-- Prove2me | solution 1 for Formalism.SLP.P.CountO.TF.submodule
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:17:35.982218+00:00
-- url     : https://prove2.me/submissions/42ac0a39-90b9-484c-93bf-8abf4c275dfe

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
namespace TF
theorem _root_.solution {X : Type} [AddCommGroup X] [Module (𝓞 E) X] (h : TF E X)
    (L : Submodule (𝓞 E) X) : TF E L := by
  intro a ha x hx
  exact Subtype.ext (h a ha x (congrArg Subtype.val hx))
end TF
end Formalism.SLP.P.CountO
