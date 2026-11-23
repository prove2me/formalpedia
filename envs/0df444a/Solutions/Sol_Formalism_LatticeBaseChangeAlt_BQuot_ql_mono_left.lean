-- Prove2me | solution 1 for Formalism.LatticeBaseChangeAlt.BQuot.ql_mono_left
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:41:16.317456+00:00
-- url     : https://prove2.me/submissions/dbcdb473-211e-49e0-b9ba-d5e6a7b46232

import Definitions.Def_Formalism_FilteredPoleLength_ReducedBasisBounds_ReductionQuotient
import Definitions.Def_Formalism_LogFactorialIndices_SignedSubspaceIndex_IdxDet
import Definitions.Def_Formalism_FilteredPoleLength_LocalDescentLevels_MemSpanBasisFun
import Theorems.Thm_Formalism_LatticeBaseChangeAlt_BQuot_ql_le_of_map

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.LatticeBaseChangeAlt
open Module
open Formalism.LatticeBaseChangeAlt.BQuot
variable {O V W : Type*} [CommRing O] [AddCommGroup V] [Module O V] [AddCommGroup W] [Module O W]
namespace Formalism.LatticeBaseChangeAlt.BQuot
theorem _root_.solution {A A' B : Submodule O V} (h : A ≤ A') : ql A B ≤ ql A' B :=
  ql_le_of_map A.subtype (fun x => h x.2) (fun _ hx => hx)
end Formalism.LatticeBaseChangeAlt.BQuot
