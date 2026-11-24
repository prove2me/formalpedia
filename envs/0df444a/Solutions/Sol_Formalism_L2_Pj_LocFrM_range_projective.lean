-- Prove2me | solution 1 for Formalism.L2.Pj.LocFrM.range_projective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:16:40.357824+00:00
-- url     : https://prove2.me/submissions/35e43a0a-2fcd-421a-a9bf-21b886558e7a

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_GenSpecLocFrM

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
theorem _root_.solution (e : Module.End O V) (he : IsIdempotentElem e) :
    Module.Projective O (LinearMap.range e) := by
  refine Module.Projective.of_split (LinearMap.range e).subtype e.rangeRestrict ?_
  apply LinearMap.ext
  rintro ⟨x, y, rfl⟩
  apply Subtype.ext
  show e (e y) = e y
  exact LinearMap.congr_fun he y
end Formalism.L2.Pj.LocFrM
