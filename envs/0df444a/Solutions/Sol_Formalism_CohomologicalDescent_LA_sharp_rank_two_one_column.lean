-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LA.sharp_rank_two_one_column
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:40:11.157895+00:00
-- url     : https://prove2.me/submissions/bc059430-d9a8-4bae-8917-0293323bbf95

import Definitions.Def_Formalism_PieriBlockIdeals_StatementLA
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LDlatLemmas
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_PadicValIntProdElevenMultiples
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_JointExactExponentStopHigh
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ProdInitialMinorsMemDetSpan
import Theorems.Thm_Formalism_CohomologicalDescent_LA_la_core
import Theorems.Thm_Formalism_CohomologicalDescent_LA_la_weyl_r2n1
import Theorems.Thm_Formalism_CohomologicalDescent_LA_la_nabla_r2n1
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LA
open Formalism.GradedWeylDivisibility
namespace Formalism.CohomologicalDescent.LA
theorem _root_.solution : SharpInclusionRankTwoOneColumn := by
  unfold SharpInclusionRankTwoOneColumn
  intro hn ν l e hl
  have hc := la_core (0 : Fin 1) (ν 0) 1 one_ne_zero l e hl
  simp only [LinearMap.mulLeft_one, Submodule.map_id] at hc
  unfold InclZ
  rw [la_nabla_r2n1, la_weyl_r2n1]
  exact hc
end Formalism.CohomologicalDescent.LA
