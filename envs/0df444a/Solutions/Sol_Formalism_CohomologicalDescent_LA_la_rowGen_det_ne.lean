-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LA.la_rowGen_det_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:03:33.39144+00:00
-- url     : https://prove2.me/submissions/c93e89d3-a460-473a-884e-d1bb65d92e82

import Definitions.Def_Formalism_PieriBlockIdeals_StatementLA
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LDlatLemmas
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_PadicValIntProdElevenMultiples
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_JointExactExponentStopHigh
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ProdInitialMinorsMemDetSpan
import Theorems.Thm_Formalism_CohomologicalDescent_LA_la_rowGen_X
import Theorems.Thm_Formalism_CohomologicalDescent_LA_fin_two_eq_zero_or_one
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
theorem _root_.solution (R : Type) [CommRing R] (a b : Fin 2) (hab : a ≠ b) :
    rowGen R a b (la_det R) = Polynomial.C (la_det R) := by
  rcases fin_two_eq_zero_or_one a with rfl | rfl <;> rcases fin_two_eq_zero_or_one b with rfl | rfl
  · exact absurd rfl hab
  · simp [la_det, la_rowGen_X] <;> ring
  · simp [la_det, la_rowGen_X] <;> ring
  · exact absurd rfl hab
end Formalism.CohomologicalDescent.LA
