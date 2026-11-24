-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LA.la_exZ_le_of_U
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:25:52.15134+00:00
-- url     : https://prove2.me/submissions/8718618e-21d5-4efa-a7c5-3a23385e6ba2

import Definitions.Def_Formalism_PieriBlockIdeals_StatementLA
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LDlatLemmas
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_PadicValIntProdElevenMultiples
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_JointExactExponentStopHigh
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ProdInitialMinorsMemDetSpan
import Theorems.Thm_Formalism_CohomologicalDescent_LA_joint_exact_z
import Theorems.Thm_Formalism_CohomologicalDescent_LA_nu_of_specialization

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
theorem _root_.solution (hA : LemmaAZ) (r : ℕ) (U : Fin r → ℤ) (hU : StrictAnti U) (h0 : ∀ a, 0 ≤ U a)
    (l : ℕ) (hl : l.Prime) : exZ r r le_rfl (nuOf U) l ≤ Formalism.RankGapBounds.JumpSetsAlt.eExp U l := by
  obtain ⟨hanti, hlam⟩ := nu_of_specialization r U hU h0
  have h := joint_exact_z hA r r le_rfl (nuOf U) hanti l hl
  rwa [hlam] at h
end Formalism.CohomologicalDescent.LA
