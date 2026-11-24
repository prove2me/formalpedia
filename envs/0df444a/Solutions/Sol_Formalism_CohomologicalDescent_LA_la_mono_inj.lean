-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LA.la_mono_inj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:53:05.618989+00:00
-- url     : https://prove2.me/submissions/c6c3ec06-bc49-4d46-b912-23591485e10b

import Definitions.Def_Formalism_PieriBlockIdeals_StatementLA
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LDlatLemmas
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_PadicValIntProdElevenMultiples
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_JointExactExponentStopHigh
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ProdInitialMinorsMemDetSpan
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
theorem _root_.solution {n : ℕ} (s : Fin n) {p q p' q' : ℕ} (h : la_mono s p q = la_mono s p' q') :
    p = p' ∧ q = q' := by
  constructor
  · simpa [la_mono, Finsupp.single_apply] using congrArg (fun m => m ((0 : Fin 2), s)) h
  · simpa [la_mono, Finsupp.single_apply] using congrArg (fun m => m ((1 : Fin 2), s)) h
end Formalism.CohomologicalDescent.LA
