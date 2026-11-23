-- Prove2me | solution 1 for Formalism.LatticeBaseChangeAlt.BQuot.ql_sup_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:41:16.522996+00:00
-- url     : https://prove2.me/submissions/7786ee0b-c2fc-4cfa-ba83-43b42a8a71b3

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
theorem _root_.solution (A B : Submodule O V) : ql (A ⊔ B) B ≤ ql A B := by
  have e := LinearMap.quotientInfEquivSupQuotient A B
  have h1 : ql (A ⊔ B) B ≤ ql A (A ⊓ B) :=
    Module.length_le_of_surjective e.toLinearMap e.surjective
  have h2 : ql A (A ⊓ B) ≤ ql A B :=
    ql_le_of_map (A := A) (S := A ⊓ B) (L := A) (P := B) A.subtype (fun x => x.2)
      (fun x hx => Submodule.mem_inf.2 ⟨x.2, hx⟩)
  exact h1.trans h2
end Formalism.LatticeBaseChangeAlt.BQuot
