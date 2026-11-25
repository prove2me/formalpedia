-- Prove2me | solution 1 for Formalism.LatticeIndexTer.LatticeIndexDeterminant.addVal_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:15:47.199381+00:00
-- url     : https://prove2.me/submissions/b184f014-c379-4eb0-88fe-e36beacdc728

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
namespace Formalism.LatticeIndexTer.LatticeIndexDeterminant
theorem _root_.solution {O ι : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (s : Finset ι) (a : ι → O) :
    IsDiscreteValuationRing.addVal O (∏ i ∈ s, a i) =
      ∑ i ∈ s, IsDiscreteValuationRing.addVal O (a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert x s hx ih =>
    rw [Finset.prod_insert hx, Finset.sum_insert hx, IsDiscreteValuationRing.addVal_mul, ih]
end Formalism.LatticeIndexTer.LatticeIndexDeterminant
