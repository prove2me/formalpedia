-- Prove2me | solution 1 for Formalism.MainNotions.Gaps.CC.Surj.walInt_neg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:00:40.640728+00:00
-- url     : https://prove2.me/submissions/682085a4-a4d7-46c2-809a-b2f5dd910639

import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Formalism_SatakeDualWeyl_DefsCS
import Definitions.Def_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_ClassCountWaLat
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix TensorProduct NumberField IsDedekindDomain
open Formalism Formalism.MainNotions Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.CC Formalism.MainNotions.Gaps.CC.Surj
open Formalism.UG
variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]
omit [Fintype n] [DecidableEq n]
namespace Formalism.MainNotions.Gaps.CC.Surj
theorem _root_.solution (S : Subring A) {M : Matrix n n A} (hM : walInt S M) :
    walInt S (-M) := fun i j => by
  rw [Matrix.neg_apply]; exact neg_mem (hM i j)
end Formalism.MainNotions.Gaps.CC.Surj
