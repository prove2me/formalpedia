-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LA.la_T_xy
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:51:30.995717+00:00
-- url     : https://prove2.me/submissions/e1a6b2c2-1b60-4e16-a389-a1d992f50fa6

import Definitions.Def_Formalism_PieriBlockIdeals_StatementLA
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LDlatLemmas
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_PadicValIntProdElevenMultiples
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_JointExactExponentStopHigh
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ProdInitialMinorsMemDetSpan

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LA
open Formalism.GradedWeylDivisibility
namespace Formalism.CohomologicalDescent.LA
theorem _root_.solution (c p q : ℕ) : la_det ℤ ^ c * la_xy ℤ (0 : Fin 2) p q ∈ detPowMulMonomialSpan c (p + q) := by
  rw [detPowMulMonomialSpan]
  exact Submodule.mem_map.mpr ⟨la_xy ℤ (0 : Fin 2) p q, Submodule.subset_span ⟨p, q, rfl, rfl⟩, rfl⟩
end Formalism.CohomologicalDescent.LA
