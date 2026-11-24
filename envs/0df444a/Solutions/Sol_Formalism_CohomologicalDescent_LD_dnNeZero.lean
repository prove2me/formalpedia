-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LD.dnNeZero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:53:08.819508+00:00
-- url     : https://prove2.me/submissions/8786e7ec-22bc-4eda-b4ed-b3966fe04a2e

import Definitions.Def_Formalism_PieriBlockIdeals_StatementLD
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_DividedPowerZeroZeroVector
import Theorems.Thm_Formalism_CohomologicalDescent_LD_ld_mu_w

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
open Formalism.GradedWeylDivisibility
namespace Formalism.CohomologicalDescent.LD
theorem _root_.solution : DnNeZero := by
  intro p w i q lam2
  unfold Dn
  rw [Finset.prod_ne_zero_iff]
  intro k _
  by_cases hk : (w : ℤ) - ((k : ℤ) - (q : ℤ)) = 0
  · have hc : (k : ℤ) - (q : ℤ) = (w : ℤ) := by omega
    rw [hc, ld_mu_w, pow_zero]
    exact one_ne_zero
  · exact pow_ne_zero _ hk
end Formalism.CohomologicalDescent.LD
