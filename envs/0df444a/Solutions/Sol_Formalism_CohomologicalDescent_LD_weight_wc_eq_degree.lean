-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LD.weight_wc_eq_degree
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:18:04.709313+00:00
-- url     : https://prove2.me/submissions/8f961f1e-3a65-45bf-b354-bf6fff946cc8

import Definitions.Def_Formalism_PieriBlockIdeals_LastGradedOfGradedAlone
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LastGradedImpliesOneBlock
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightShiftEqDetMul
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LEhwLemmas
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightProdLeadingMinors
import Theorems.Thm_Formalism_GradedWeylDivisibility_lgraded_weight_rowW
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
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
theorem _root_.solution {r : ℕ} (c : Fin r) (d : Fin r × Fin r →₀ ℕ) :
    Finsupp.weight (columnWeight c) d = ((Finsupp.weight (rowW r r) d c : ℕ) : ℤ) := by
  rw [lgraded_weight_rowW, Finsupp.weight_apply, Finsupp.weight_apply, Finsupp.sum, Finsupp.sum]
  push_cast
  refine Finset.sum_congr rfl fun v _ => ?_
  simp [columnWeight]
end Formalism.CohomologicalDescent.LD
