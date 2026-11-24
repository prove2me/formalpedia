-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LD.shape_total_degree
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:08:42.926258+00:00
-- url     : https://prove2.me/submissions/7076c1bc-6270-495f-b7de-2bb9b00b960b

import Definitions.Def_Formalism_PieriBlockIdeals_LastGradedOfGradedAlone
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LastGradedImpliesOneBlock
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightShiftEqDetMul
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LEhwLemmas
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightProdLeadingMinors
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_GradedWeylDivisibility_sum_min_eq_shapeDeg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open MvPolynomial
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LD
open Formalism.GradedWeylDivisibility Formalism.CohomologicalDescent.LA
namespace Formalism.CohomologicalDescent.LD
theorem _root_.solution {r K : ℕ} (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ r) :
    ∑ k, sz k = ∑ t : Fin r, shapeDeg sz t := by
  have e := sum_min_eq_shapeDeg sz hsz r
  have e1 : ∀ k', min r (sz k') = sz k' := fun k' => min_eq_right (hsz k')
  simp only [e1] at e
  rw [Finset.filter_true_of_mem (fun t _ => t.isLt)] at e
  exact e
end Formalism.CohomologicalDescent.LD
