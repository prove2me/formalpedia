-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LA.choose_dvd_choose_mul_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:53:05.359372+00:00
-- url     : https://prove2.me/submissions/d7f9578e-a6fd-4e08-b4ce-7e97b1f770b1

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
theorem _root_.solution (p k q : ℕ) :
    (p + (k + q)).choose (k + q) ∣ (p + k + q).choose q * (p + k).choose k := by
  have key := Nat.choose_mul (n := p + k + q) (k := k + q) (s := q) (by omega)
  rw [show p + k + q - q = p + k by omega, show k + q - q = k by omega] at key
  rw [show p + (k + q) = p + k + q by omega]
  exact ⟨(k + q).choose q, by linarith [key]⟩
end Formalism.CohomologicalDescent.LA
