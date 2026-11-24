-- Prove2me | solution 1 for Formalism.IncomingBounds.LatticeIndexAlt.idx_comap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T09:43:14.265201+00:00
-- url     : https://prove2.me/submissions/9b03ef50-4873-43b7-bead-07fd65fa6711

import Definitions.Def_Formalism_IncomingBounds_IndexLastStep
import Definitions.Def_Formalism_LogFactorialIndices_SignedSubspaceIndex_SubspaceLatticeIndexSigned
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_IndexLastReductionHolds
import Theorems.Thm_Formalism_IncomingBounds_LatticeIndexAlt_qlen_comap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Module
open scoped Pointwise
open Formalism Formalism.IncomingBounds Formalism.IncomingBounds.LatticeIndexAlt
open Formalism.LatticeIndexTer
variable {O K X : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K]
  [Algebra O K] [IsFractionRing O K] [AddCommGroup X] [Module K X] [Module O X]
  [IsScalarTower O K X]
namespace Formalism.IncomingBounds.LatticeIndexAlt
theorem _root_.solution (W : Submodule K X) (A B : Submodule O X) :
    idx O W (A.comap ((W.subtype).restrictScalars O)) (B.comap ((W.subtype).restrictScalars O)) =
      idx O X (A ⊓ W.restrictScalars O) (B ⊓ W.restrictScalars O) := by
  unfold idx
  rw [qlen_comap W A B, qlen_comap W B A]
end Formalism.IncomingBounds.LatticeIndexAlt
