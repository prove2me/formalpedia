-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LA.la_rowGen_det_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:03:19.791889+00:00
-- url     : https://prove2.me/submissions/42e41259-a259-4ec8-ae34-eada047ef2ea

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
theorem _root_.solution (R : Type) [CommRing R] (a : Fin 2) :
    rowGen R a a (la_det R) = Polynomial.C (la_det R) * (1 + Polynomial.X) := by
  rcases fin_two_eq_zero_or_one a with rfl | rfl
  · simp [la_det, la_rowGen_X] <;> ring
  · simp [la_det, la_rowGen_X] <;> ring
end Formalism.CohomologicalDescent.LA
