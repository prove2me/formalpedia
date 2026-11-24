-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LD.block_weight_last_le_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:08:42.104079+00:00
-- url     : https://prove2.me/submissions/666ffd51-6928-4150-9766-c71958126293

import Definitions.Def_Formalism_PieriBlockIdeals_LastGradedOfGradedAlone
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LastGradedImpliesOneBlock
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightShiftEqDetMul
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LEhwLemmas
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightProdLeadingMinors

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
theorem _root_.solution (p q w M : ℕ) (κ : Fin q → ℕ) (hκ : ∀ b, κ b ≤ M) (hw : w ≤ M) (a : Fin (q + p)) :
    blockWtLast p q w κ a ≤ M := by
  unfold blockWtLast
  refine Fin.addCases (fun b => ?_) (fun b => ?_) a
  · rw [Fin.append_left]
    exact hκ b
  · rw [Fin.append_right]
    exact hw
end Formalism.CohomologicalDescent.LD
