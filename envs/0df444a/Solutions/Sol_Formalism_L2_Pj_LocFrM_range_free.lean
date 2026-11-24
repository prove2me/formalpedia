-- Prove2me | solution 1 for Formalism.L2.Pj.LocFrM.range_free
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:23:07.332212+00:00
-- url     : https://prove2.me/submissions/aa18ce71-6d8e-4ca3-abbb-c0a347f047cd

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_GenSpecLocFrM
import Theorems.Thm_Formalism_L2_Pj_LocFrM_range_projective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.LocFrM
open TensorProduct
variable {O : Type*} [CommRing O] [IsLocalRing O] {V : Type*} [AddCommGroup V] [Module O V]
  [Module.Free O V] [Module.Finite O V]
namespace Formalism.L2.Pj.LocFrM
theorem _root_.solution (e : Module.End O V) (he : IsIdempotentElem e) : Module.Free O (LinearMap.range e) := by
  haveI := range_projective e he
  haveI : Module.FinitePresentation O (LinearMap.range e) := Module.finitePresentation_of_projective _ _
  exact Module.free_of_flat_of_isLocalRing
end Formalism.L2.Pj.LocFrM
