-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LR.lrb_pi_single_cast
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:02:19.083109+00:00
-- url     : https://prove2.me/submissions/bc43ed70-1794-4c4b-85ce-66e0fe897e6c

import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_GradedWeylDivisibility_StatementE
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_FockQHW
import Definitions.Def_Formalism_PieriBlockIdeals_StatementLD
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_DividedPowerZeroZeroVector
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LrbPiSingleCast
import Theorems.Thm_Formalism_CohomologicalDescent_LR_lrb_cast_ne_nat

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
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LR
open Formalism.GradedWeylDivisibility
variable (R : Type*) [CommRing R] (p q : ℕ)
namespace Formalism.CohomologicalDescent.LR
theorem _root_.solution (a : Fin p) : lrbPi p q (Pi.single (Fin.castAdd q a) 1) = 0 := by
  funext t
  change (Pi.single (Fin.castAdd q a) 1 : Fin (p + q) → ℕ) (Fin.natAdd p t) = 0
  rw [Pi.single_eq_of_ne (lrb_cast_ne_nat p q a t).symm]
end Formalism.CohomologicalDescent.LR
