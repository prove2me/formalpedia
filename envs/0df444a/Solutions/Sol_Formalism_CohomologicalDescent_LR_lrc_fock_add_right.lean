-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LR.lrc_fock_add_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:38:10.071301+00:00
-- url     : https://prove2.me/submissions/2f02706d-97c5-4459-8356-e8ecc330f866

import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_GradedWeylDivisibility_StatementE
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_FockQHW
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_FockQWordAdj
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LrcFockZeroRight
import Theorems.Thm_Formalism_GradedWeylDivisibility_fockQBilin
import Theorems.Thm_Formalism_GradedWeylDivisibility_fockQPos


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
namespace Formalism.CohomologicalDescent.LR
theorem _root_.solution {σ : Type} (f g g' : MvPolynomial σ ℚ) : fockQ f (g + g') = fockQ f g + fockQ f g' := by
  rw [(fockQPos σ f (g + g')).1, (fockQBilin σ g g' f 1).1, (fockQPos σ g f).1, (fockQPos σ g' f).1]
end Formalism.CohomologicalDescent.LR
