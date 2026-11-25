-- Prove2me | solution 1 for Formalism.LatticeBaseChangeAlt.BasisReduction.q_chain
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:23:12.636306+00:00
-- url     : https://prove2.me/submissions/bbc82abc-21e1-4ae6-960a-44e8a192478f

import Definitions.Def_Formalism_FilteredPoleLength_ReducedBasisBounds_ReductionQuotient
import Definitions.Def_Formalism_LogFactorialIndices_LogProductFormula
import Definitions.Def_Formalism_FilteredPoleLength_LocalDescentLevels_ReductionQuotient
import Theorems.Thm_P2M_Formalism_LatticeIndexTer_subgroupData_length_chain__bd85a5aaefa7


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
theorem _root_.solution {A B C : Submodule O X} (hAB : A ≤ B) (hBC : B ≤ C) :
    q C A = q C B + q B A := by
  rw [add_comm]
  exact length_chain' hAB hBC
end Formalism.LatticeBaseChangeAlt.BasisReduction
