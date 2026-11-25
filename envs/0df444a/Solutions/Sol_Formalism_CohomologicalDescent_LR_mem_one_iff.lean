-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LR.mem_one_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:15:23.816488+00:00
-- url     : https://prove2.me/submissions/7731dd64-906f-48a0-af1e-cce5e1c03817

import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_GradedWeylDivisibility_StatementE
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_FockQHW
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_FockQWordAdj
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LrcFockZeroRight

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
theorem _root_.solution (l : ℕ) (x : ℚ) : x ∈ (1 : Submodule (Zl l) ℚ) ↔ x ∈ Zl l := by
  rw [Submodule.mem_one]
  constructor
  · rintro ⟨y, rfl⟩
    exact y.2
  · intro hx
    exact ⟨⟨x, hx⟩, rfl⟩
end Formalism.CohomologicalDescent.LR
