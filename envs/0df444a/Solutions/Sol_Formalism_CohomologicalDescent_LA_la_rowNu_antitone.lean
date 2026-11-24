-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LA.la_rowNu_antitone
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:53:11.510155+00:00
-- url     : https://prove2.me/submissions/6c836b39-3f19-4acc-92c7-c86d6c91d6ed

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
theorem _root_.solution {r n : ℕ} (ν : Fin n → ℕ) (hν : Antitone ν) :
    Antitone (rowNu (r := r) ν) := by
  intro a b hab
  have hab' : a.val ≤ b.val := hab
  unfold rowNu
  by_cases hb : b.val < n
  · have ha : a.val < n := by omega
    rw [dif_pos hb, dif_pos ha]
    exact hν (show (⟨a.val, ha⟩ : Fin n) ≤ ⟨b.val, hb⟩ from hab')
  · rw [dif_neg hb]
    exact Nat.zero_le _
end Formalism.CohomologicalDescent.LA
