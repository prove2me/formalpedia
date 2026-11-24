-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LD.eq_sum_weighted_components
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:17:10.614139+00:00
-- url     : https://prove2.me/submissions/e3115688-2fbd-4bc7-9d35-9d0351d0569a

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
theorem _root_.solution {r : ℕ} (x : MvPolynomial (Fin r × Fin r) ℤ) :
    ∃ S : Finset (Fin r → ℕ), x = ∑ μ ∈ S, weightedHomogeneousComponent (rowW r r) μ x :=
  ⟨_, by rw [← finsum_eq_sum _ (weightedHomogeneousComponent_finsupp x), sum_weightedHomogeneousComponent]⟩
end Formalism.CohomologicalDescent.LD
