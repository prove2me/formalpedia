-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LA.lemma_a_real_of_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:26:33.74836+00:00
-- url     : https://prove2.me/submissions/630669c0-0f88-4251-92fa-f239628fa74b

import Definitions.Def_Formalism_PieriBlockIdeals_StatementLA
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LDlatLemmas
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_PadicValIntProdElevenMultiples
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_JointExactExponentStopHigh
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ProdInitialMinorsMemDetSpan
import Theorems.Thm_Formalism_CohomologicalDescent_LA_la_incl_R_of_Z

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
theorem _root_.solution : LemmaAROfZ := by
  unfold LemmaAROfZ LemmaAR
  intro hZ R _ _ r n hn ν hν l hl hu x hx
  exact la_incl_R_of_Z R r n hn ν l _ hu (hZ r n hn ν hν l hl) x hx
end Formalism.CohomologicalDescent.LA
