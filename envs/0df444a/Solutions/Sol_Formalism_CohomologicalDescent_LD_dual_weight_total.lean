-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LD.dual_weight_total
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:19:52.596841+00:00
-- url     : https://prove2.me/submissions/b52d0b99-e420-48fb-bf93-64d32ffe0d84

import Definitions.Def_Formalism_PieriBlockIdeals_LastGradedOfGradedAlone
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LastGradedImpliesOneBlock
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightShiftEqDetMul
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LEhwLemmas
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightProdLeadingMinors
import Theorems.Thm_Formalism_CohomologicalDescent_LD_sum_complement_add_sum

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
theorem _root_.solution {r : ℕ} (M : ℕ) (ν : Fin r → ℕ) (hM : ∀ a, ν a ≤ M) :
    ∑ a, dualWt M ν a + ∑ a, ν a = r * M := by
  have h0 : ∑ a, dualWt M ν a = ∑ a, (M - ν a) := Equiv.sum_comp Fin.revPerm fun a => M - ν a
  rw [h0]
  exact sum_complement_add_sum M ν hM
end Formalism.CohomologicalDescent.LD
