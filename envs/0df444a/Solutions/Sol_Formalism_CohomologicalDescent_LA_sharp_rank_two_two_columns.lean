-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LA.sharp_rank_two_two_columns
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:48:41.735573+00:00
-- url     : https://prove2.me/submissions/ee95ef51-52a1-4363-89d7-6c2d83b2046e

import Definitions.Def_Formalism_PieriBlockIdeals_StatementLA
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LDlatLemmas
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_PadicValIntProdElevenMultiples
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_JointExactExponentStopHigh
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ProdInitialMinorsMemDetSpan
import Theorems.Thm_Formalism_CohomologicalDescent_LA_la_core
import Theorems.Thm_Formalism_CohomologicalDescent_LA_la_weyl_r2n2
import Theorems.Thm_Formalism_CohomologicalDescent_LA_la_det_ne
import Theorems.Thm_Formalism_CohomologicalDescent_LA_la_nabla_r2n2

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
theorem _root_.solution : SharpInclusionRankTwoTwoColumns := by
  unfold SharpInclusionRankTwoTwoColumns
  intro hn ν hν l e hl
  have hc := la_core (0 : Fin 2) (ν 0 - ν 1) (la_det ℤ ^ ν 1) (pow_ne_zero _ la_det_ne) l e hl
  unfold InclZ
  rw [la_nabla_r2n2 hn ν hν, la_weyl_r2n2 ℤ hn ν]
  exact hc
end Formalism.CohomologicalDescent.LA
