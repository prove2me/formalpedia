-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LA.exact_z_specialization
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:29:30.847862+00:00
-- url     : https://prove2.me/submissions/39781f2e-c31e-4d8a-9efb-0e31111ca877

import Definitions.Def_Formalism_PieriBlockIdeals_StatementLA
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LDlatLemmas
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_PadicValIntProdElevenMultiples
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_JointExactExponentStopHigh
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ProdInitialMinorsMemDetSpan
import Theorems.Thm_Formalism_CohomologicalDescent_LA_la_uniform

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
theorem _root_.solution : ExZSpec := by
  unfold ExZSpec
  intro r n hn ν hν l hl
  obtain ⟨N, hN0, hN⟩ := la_uniform r n hn ν hν
  obtain ⟨v, m, hm, hNe⟩ := Nat.exists_eq_pow_mul_and_not_dvd hN0 l hl.ne_one
  have hv : InclZ r n hn ν l v := by
    unfold InclZ
    refine ⟨m, hm, fun x hx => ?_⟩
    rw [mul_comm m, ← hNe]
    exact hN x hx
  exact Nat.sInf_mem (s := {e : ℕ | InclZ r n hn ν l e}) ⟨v, hv⟩
end Formalism.CohomologicalDescent.LA
