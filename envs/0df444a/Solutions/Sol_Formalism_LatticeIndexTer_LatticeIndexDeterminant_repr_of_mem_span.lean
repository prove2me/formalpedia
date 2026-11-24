-- Prove2me | solution 1 for Formalism.LatticeIndexTer.LatticeIndexDeterminant.repr_of_mem_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:35:17.155803+00:00
-- url     : https://prove2.me/submissions/95b671f2-ccae-44a9-a975-2287629beb0d

import Definitions.Def_Formalism_LogFactorialIndices_StatementIdx
import Definitions.Def_Lemmata_DiscreteValuationQuotients_LenQuotSpan
import Definitions.Def_Lemmata_GeneralBFactSecondExtra_Key
import Definitions.Def_Formalism_LogFactorialIndices_SignedSubspaceIndex_IdxDet

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Submodule
noncomputable section
open Formalism Formalism.LatticeIndexTer Formalism.LatticeIndexTer.LatticeIndexDeterminant
variable {O K Y ι : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K]
  [Algebra O K] [IsFractionRing O K] [AddCommGroup Y] [Module K Y] [Module O Y]
  [IsScalarTower O K Y] [Fintype ι] [DecidableEq ι]
namespace Formalism.LatticeIndexTer.LatticeIndexDeterminant
theorem _root_.solution (b : Basis ι K Y)
    (li : LinearIndependent O b) (z : Submodule.span O (Set.range b)) (i : ι) :
    b.repr z i = algebraMap O K ((Basis.span li).repr z i) := by
  have hz : (z : Y) = ∑ j, algebraMap O K ((Basis.span li).repr z j) • b j := by
    conv_lhs => rw [← (Basis.span li).sum_repr z]
    simp [Basis.span_apply, algebraMap_smul]
  rw [hz, b.repr_sum_self]
end Formalism.LatticeIndexTer.LatticeIndexDeterminant
