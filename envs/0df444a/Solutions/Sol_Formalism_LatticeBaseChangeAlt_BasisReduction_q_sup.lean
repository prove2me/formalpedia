-- Prove2me | solution 1 for Formalism.LatticeBaseChangeAlt.BasisReduction.q_sup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:33:56.802394+00:00
-- url     : https://prove2.me/submissions/850048db-82ee-4ae1-93d9-e9934011ac33

import Definitions.Def_Formalism_FilteredPoleLength_ReducedBasisBounds_ReductionQuotient
import Definitions.Def_Formalism_LogFactorialIndices_LogProductFormula
import Definitions.Def_Formalism_FilteredPoleLength_LocalDescentLevels_ReductionQuotient
import Theorems.Thm_Formalism_LatticeBaseChangeAlt_BasisReduction_q_congr

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
theorem _root_.solution (A B : Submodule O X) : q (A ⊔ B) B = q A B := by
  have h := (LinearMap.quotientInfEquivSupQuotient A B).length_eq
  have h2 : q A (A ⊓ B) = q A B := q_congr A (by simp)
  exact h.symm.trans h2
end Formalism.LatticeBaseChangeAlt.BasisReduction
