-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LD.dnPos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:10:11.434839+00:00
-- url     : https://prove2.me/submissions/00bbddc7-7b4e-450a-92cb-71430062c528

import Definitions.Def_Formalism_PieriBlockIdeals_StatementLD
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_DividedPowerZeroZeroVector
import Theorems.Thm_Formalism_CohomologicalDescent_LD_muRange

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
theorem _root_.solution : DnPos := by
  intro p w i q lam2 hw
  unfold Dn
  refine Finset.prod_pos fun k _ => ?_
  by_cases hmu : mu p w i lam2 ((k : ℤ) - (q : ℤ)) = 0
  · rw [hmu, pow_zero]
    exact one_pos
  · have hlt := (muRange p w i q 0 lam2 _ (fun b => ⟨Nat.zero_le _, hw b⟩) hmu).2
    exact pow_pos (by omega) _
end Formalism.CohomologicalDescent.LD
