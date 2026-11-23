-- Prove2me | solution 1 for Formalism.RepresentationBoundsCohomology.LOC.mem_mulSub
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:31:59.558563+00:00
-- url     : https://prove2.me/submissions/8c19f635-979d-4db9-82ee-a3bf1634bd8c

import Definitions.Def_Formalism_WachLatticeTwists_LatticeDualFibres_Statement
import Definitions.Def_Formalism_WachLatticeTwists_TorsionLengthCounts_RowCol
import Definitions.Def_Formalism_WachLatticeTwists_TorsionLengthCounts_SubmoduleLengthBoundStatement
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LengthEqKerAddRange
import Definitions.Def_Formalism_WachLatticeTwists_LatticeDualFibres_LatticeDualProofs_QuotLen

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open Formalism.NG (KO annih)
noncomputable section
open Formalism Formalism.RepresentationBoundsCohomology Formalism.RepresentationBoundsCohomology.LOC
open Module
variable {O : Type u} [CommRing O]
namespace Formalism.RepresentationBoundsCohomology.LOC
theorem _root_.solution {a : O} {M : Type u} [AddCommGroup M] [Module O M] (x : M) :
    x ∈ mulSub a M ↔ ∃ m, a • m = x := by
  simp only [mulSub, LinearMap.mem_range, LinearMap.lsmul_apply]
end Formalism.RepresentationBoundsCohomology.LOC
