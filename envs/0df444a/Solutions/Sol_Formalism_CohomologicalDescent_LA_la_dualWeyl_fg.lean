-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LA.la_dualWeyl_fg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:51:23.825483+00:00
-- url     : https://prove2.me/submissions/00ea6267-1ad2-4f10-b773-f901608f5109

import Definitions.Def_Formalism_PieriBlockIdeals_StatementLA
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LDlatLemmas
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_PadicValIntProdElevenMultiples
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_JointExactExponentStopHigh
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ProdInitialMinorsMemDetSpan
import Theorems.Thm_Formalism_GradedWeylDivisibility_lclosedeq_weight_sum
import Theorems.Thm_Formalism_GradedWeylDivisibility_mem_dualWeyl_iff


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
theorem _root_.solution (r n : ℕ) (ν : Fin n → ℕ) : (dualWeyl ℤ r n ν).FG := by
  have h : dualWeyl ℤ r n ν ≤ homogeneousSubmodule (Fin r × Fin n) ℤ (∑ s, ν s) := by
    intro f hf
    have h1 := (mem_dualWeyl_iff.1 hf).1
    rw [mem_homogeneousSubmodule]
    intro m hm
    rw [← lclosedeq_weight_sum, h1 hm]
  exact Submodule.FG.of_le (homogeneousSubmodule_fg _ _ _) h
end Formalism.CohomologicalDescent.LA
