-- Prove2me | solution 1 for Formalism.LatticeBaseChangeAlt.BasisReduction.q_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:49:32.492129+00:00
-- url     : https://prove2.me/submissions/51590f39-1ddb-4161-b76b-3c1166e6e74c

import Definitions.Def_Formalism_FilteredPoleLength_ReducedBasisBounds_ReductionQuotient
import Definitions.Def_Formalism_LogFactorialIndices_LogProductFormula
import Definitions.Def_Formalism_FilteredPoleLength_LocalDescentLevels_ReductionQuotient
import Theorems.Thm_Formalism_LatticeBaseChangeAlt_BasisReduction_len_comap_le

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
open Formalism.LatticeBaseChangeAlt.BasisReduction
open Formalism.LatticeIndexTer.subgroupData
variable {O X : Type} [CommRing O] [AddCommGroup X] [Module O X]
namespace Formalism.LatticeBaseChangeAlt.BasisReduction
theorem _root_.solution (N : Submodule O X) : q ⊤ N = Module.length O (X ⧸ N) := by
  apply le_antisymm
  · exact len_comap_le _ _
  · have h := len_comap_le (Submodule.topEquiv (R := O) (M := X)).symm.toLinearMap
      (N.comap (⊤ : Submodule O X).subtype)
    refine le_trans (le_of_eq ?_) h
    congr 2
end Formalism.LatticeBaseChangeAlt.BasisReduction
