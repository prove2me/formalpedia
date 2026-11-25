-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LR.mem_locSpan
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:20:21.675323+00:00
-- url     : https://prove2.me/submissions/3853536f-89cf-44da-b8f2-368b669b063c

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
theorem _root_.solution (l : ℕ) (hl : l.Prime) {V : Type*} [AddCommGroup V] [Module ℚ V] (M : AddSubgroup V) (v : V) :
    v ∈ locSpan l hl M ↔ ∃ m : ℤ, ¬ (l : ℤ) ∣ m ∧ m • v ∈ M := Iff.rfl
end Formalism.CohomologicalDescent.LR
