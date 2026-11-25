-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LA.incl_z_monotone
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:20:36.067973+00:00
-- url     : https://prove2.me/submissions/3a9f62be-afdf-4228-8f0c-588141eedc2c

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
theorem _root_.solution : InclZMono := by
  unfold InclZMono InclZ
  intro r n hn ν l e e' hee' hI
  obtain ⟨m, hm, h⟩ := hI
  refine ⟨m, hm, fun x hx => ?_⟩
  have e1 : m * l ^ e' = l ^ (e' - e) * (m * l ^ e) := by
    rw [mul_left_comm, ← pow_add, Nat.sub_add_cancel hee']
  rw [e1, Nat.cast_mul, mul_smul]
  exact Submodule.smul_mem _ _ (h x hx)
end Formalism.CohomologicalDescent.LA
