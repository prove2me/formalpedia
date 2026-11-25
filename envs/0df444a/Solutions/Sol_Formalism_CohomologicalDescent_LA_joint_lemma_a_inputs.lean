-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LA.joint_lemma_a_inputs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:37:26.840338+00:00
-- url     : https://prove2.me/submissions/e9c2d0f0-4107-4341-8cd9-86edbba4459d

import Definitions.Def_Formalism_PieriBlockIdeals_StatementLA
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LDlatLemmas
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_PadicValIntProdElevenMultiples
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_JointExactExponentStopHigh
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ProdInitialMinorsMemDetSpan
import Theorems.Thm_Formalism_CohomologicalDescent_LA_joint_lemma_a_full
import Theorems.Thm_Formalism_CohomologicalDescent_LA_la_exZ_le_of_U
import Theorems.Thm_Formalism_CohomologicalDescent_Joint_cloud_anti
import Theorems.Thm_Formalism_CohomologicalDescent_Joint_rest_anti


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
theorem _root_.solution : JointLemmaAInputs := by
  intro ι D W hA hE hP l hl hexc
  refine ⟨joint_lemma_a_full ι D W hA hE l hl hexc, fun τ hτ => ⟨?_, ?_⟩⟩
  · exact (hP l hl hexc τ hτ).1.trans (la_exZ_le_of_U hA D.k (W.cloud τ)
      (Formalism.CohomologicalDescent.Joint.cloud_anti W τ) (fun a => (W.inRange τ _).1) l hl)
  · exact (hP l hl hexc τ hτ).2.trans (la_exZ_le_of_U hA (D.Nr - D.k) (W.rest τ)
      (Formalism.CohomologicalDescent.Joint.rest_anti W τ) (fun a => (W.inRange τ _).1) l hl)
end Formalism.CohomologicalDescent.LA
