-- Prove2me | solution 1 for Formalism.LatticeBaseChangeAlt.BQuot.ql_le_of_le_sup
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:44:46.442124+00:00
-- url     : https://prove2.me/submissions/1e3ef671-11d1-42b6-9f44-e018093a1d7b

import Definitions.Def_Formalism_FilteredPoleLength_ReducedBasisBounds_ReductionQuotient
import Definitions.Def_Formalism_LogFactorialIndices_SignedSubspaceIndex_IdxDet
import Definitions.Def_Formalism_FilteredPoleLength_LocalDescentLevels_MemSpanBasisFun
import Theorems.Thm_Formalism_LatticeBaseChangeAlt_BQuot_ql_mono_left
import Theorems.Thm_Formalism_LatticeBaseChangeAlt_BQuot_ql_sup_le

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
theorem _root_.solution {A A' B : Submodule O V} (h : A ≤ A' ⊔ B) : ql A B ≤ ql A' B :=
  (ql_mono_left h).trans (ql_sup_le A' B)
end Formalism.LatticeBaseChangeAlt.BQuot
