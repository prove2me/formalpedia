-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LD.lastGradedOfGraded
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:45:33.754662+00:00
-- url     : https://prove2.me/submissions/31ba3803-fb31-4cdf-98e8-53eb6abd233e

import Definitions.Def_Formalism_PieriBlockIdeals_LastGradedOfGradedAlone
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LastGradedImpliesOneBlock
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightShiftEqDetMul
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LEhwLemmas
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightProdLeadingMinors
import Theorems.Thm_Formalism_CohomologicalDescent_LD_d_n_empty_eq_one
import Theorems.Thm_Formalism_CohomologicalDescent_LD_last_graded_at_of_exp_dual

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LD
open Formalism.GradedWeylDivisibility Formalism.CohomologicalDescent.LA
namespace Formalism.CohomologicalDescent.LD
theorem _root_.solution : LastGradedOfGraded := by
  intro hE hD l p q w M lam2 ξ hl ha hb hξ
  rcases Nat.eq_zero_or_pos q with hq | hq
  · subst hq
    have h := last_graded_at_of_exp_dual hE hD l p 0 w (max M w) lam2 ξ hl ha (fun b => b.elim0) (le_max_right _ _) hξ
    intro i' eL heL i μ hd hd2
    have h1 := h i' eL heL i μ hd hd2
    rw [d_n_empty_eq_one] at h1 ⊢
    exact h1
  · exact last_graded_at_of_exp_dual hE hD l p q w M lam2 ξ hl ha hb ((hb ⟨0, hq⟩).1.trans (hb ⟨0, hq⟩).2) hξ
end Formalism.CohomologicalDescent.LD
