-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LA.highest_weight_rank_two
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:02:33.730171+00:00
-- url     : https://prove2.me/submissions/6bd59161-d127-428d-ad58-f2a130c006fb

import Definitions.Def_Formalism_PieriBlockIdeals_StatementLA
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LDlatLemmas
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_PadicValIntProdElevenMultiples
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_JointExactExponentStopHigh
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ProdInitialMinorsMemDetSpan
import Theorems.Thm_Formalism_CohomologicalDescent_LA_la_lpMinor_one
import Theorems.Thm_Formalism_CohomologicalDescent_LA_la_lpMinor_two

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
theorem _root_.solution (R : Type) [CommRing R] (hn : 2 ≤ 2) (ν : Fin 2 → ℕ) :
    hw R hn ν = la_det R ^ ν 1 * la_xy R (0 : Fin 2) (ν 0 - ν 1) 0 := by
  show ∏ s : Fin 2, (lpMinor R (s.val + 1) (by omega) (by omega)) ^ (ν s - nuNext ν s) = _
  rw [Fin.prod_univ_two, show nuNext ν 0 = ν 1 from dif_pos (by decide),
    show nuNext ν 1 = 0 from dif_neg (by decide), Nat.sub_zero]
  have e1 := la_lpMinor_one R (r := 2) (n := 2) ((0 : Fin 2).val + 1) (by decide) (by decide) (by decide)
  have e2 := la_lpMinor_two R ((1 : Fin 2).val + 1) (by decide) (by decide) (by decide)
  rw [e1, e2, la_xy, pow_zero, mul_one]
  exact mul_comm _ _
end Formalism.CohomologicalDescent.LA
