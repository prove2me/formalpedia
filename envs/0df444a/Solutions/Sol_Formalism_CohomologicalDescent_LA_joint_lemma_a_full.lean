-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LA.joint_lemma_a_full
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:16:08.190995+00:00
-- url     : https://prove2.me/submissions/130ab1a1-73d5-4bb1-8994-04ae96b655c6

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
theorem _root_.solution : JointLemmaAFull := by
  intro ι D W hA hE l hl hexc τ
  obtain ⟨h1, h2⟩ := nu_of_specialization D.Nr (W.U τ) (W.anti τ) (fun a => (W.inRange τ a).1)
  have h3 := joint_exact_z hA D.Nr D.Nr le_rfl (nuOf (W.U τ)) h1 l hl
  rw [h2] at h3
  exact (hE l hl hexc τ).trans h3
end Formalism.CohomologicalDescent.LA
