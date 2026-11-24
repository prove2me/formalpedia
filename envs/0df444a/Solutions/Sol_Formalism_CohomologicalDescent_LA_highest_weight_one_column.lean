-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LA.highest_weight_one_column
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:02:31.857561+00:00
-- url     : https://prove2.me/submissions/30ee360b-8c79-4ac9-829e-8c948f83e4f1

import Definitions.Def_Formalism_PieriBlockIdeals_StatementLA
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LDlatLemmas
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_PadicValIntProdElevenMultiples
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_JointExactExponentStopHigh
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ProdInitialMinorsMemDetSpan
import Theorems.Thm_Formalism_CohomologicalDescent_LA_la_lpMinor_one

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
theorem _root_.solution (R : Type) [CommRing R] {r : ℕ} (hn : 1 ≤ r) (ν : Fin 1 → ℕ) :
    hw R hn ν = X ((⟨0, hn⟩ : Fin r), (0 : Fin 1)) ^ ν 0 := by
  show ∏ s : Fin 1, (lpMinor R (s.val + 1) (by omega) (by omega)) ^ (ν s - nuNext ν s) = _
  rw [Fin.prod_univ_one, show nuNext ν 0 = 0 from dif_neg (by decide), Nat.sub_zero]
  exact congrArg (· ^ ν 0) (la_lpMinor_one R _ rfl _ _)
end Formalism.CohomologicalDescent.LA
