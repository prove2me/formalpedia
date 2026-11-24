-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LR.lrc_fock_smul_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:38:01.617225+00:00
-- url     : https://prove2.me/submissions/85745f5d-c82a-414a-b7f4-e413f6647688

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
theorem _root_.solution {σ : Type} (c : ℚ) (f g : MvPolynomial σ ℚ) : fockQ f (c • g) = c * fockQ f g := by
  rw [(fockQPos σ f (c • g)).1, (fockQBilin σ g 0 f c).2, (fockQPos σ g f).1]
end Formalism.CohomologicalDescent.LR
