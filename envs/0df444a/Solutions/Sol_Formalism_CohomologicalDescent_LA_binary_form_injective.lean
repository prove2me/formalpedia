-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LA.binary_form_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:18:16.485992+00:00
-- url     : https://prove2.me/submissions/7528f587-97c8-4632-acdc-7bbd10d97d7a

import Definitions.Def_Formalism_PieriBlockIdeals_StatementLA
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LDlatLemmas
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_PadicValIntProdElevenMultiples
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_JointExactExponentStopHigh
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ProdInitialMinorsMemDetSpan
import Theorems.Thm_Formalism_CohomologicalDescent_LA_la_coeff_binForm

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
theorem _root_.solution : BinFormInj := by
  unfold BinFormInj
  intro R _ d c c' h
  funext i
  rw [← la_coeff_binForm R d c i, ← la_coeff_binForm R d c' i, h]
end Formalism.CohomologicalDescent.LA
