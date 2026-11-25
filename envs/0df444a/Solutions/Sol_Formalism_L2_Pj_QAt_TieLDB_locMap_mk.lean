-- Prove2me | solution 1 for Formalism.L2.Pj.QAt.TieLDB.locMap_mk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:42:48.280866+00:00
-- url     : https://prove2.me/submissions/41600750-6744-4509-b6c6-785067c69fd8

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_TieLDB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.QAt Formalism.L2.Pj.QAt.TieLDB
open Module
variable {A : Type*} [CommRing A] (p : Ideal A) [p.IsPrime]
  {V : Type*} [AddCommGroup V] [Module A V] [Module (Localization.AtPrime p) V]
  [IsScalarTower A (Localization.AtPrime p) V]
variable (H G : Submodule A V)
namespace Formalism.L2.Pj.QAt.TieLDB
theorem _root_.solution (h : H) :
    locMap p H G (Submodule.Quotient.mk h) = Submodule.Quotient.mk (inc p H h) := rfl
end Formalism.L2.Pj.QAt.TieLDB
