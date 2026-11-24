-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LA.choose_dvd_choose_mul_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:53:04.180972+00:00
-- url     : https://prove2.me/submissions/5e26868d-f10a-40d0-866a-5dbb802a1ce4

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
    (p + k + q).choose q ∣ (p + (q + k)).choose (q + k) * (q + k).choose k := by
  have key := Nat.choose_mul (n := p + k + q) (k := q + k) (s := q) (by omega)
  rw [show p + k + q - q = p + k by omega, show q + k - q = k by omega] at key
  have hs : (q + k).choose k = (q + k).choose q := (Nat.choose_symm_add).symm
  rw [show p + (q + k) = p + k + q by omega, hs]
  exact ⟨(p + k).choose k, by linarith [key]⟩
end Formalism.CohomologicalDescent.LA
