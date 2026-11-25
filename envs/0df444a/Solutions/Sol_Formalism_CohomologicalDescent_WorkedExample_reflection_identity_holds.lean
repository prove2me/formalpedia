-- Prove2me | solution 1 for Formalism.CohomologicalDescent.WorkedExample.reflection_identity_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:24:30.905669+00:00
-- url     : https://prove2.me/submissions/0800ab3e-1eec-4df0-8677-cf81d5789f8d

import Mathlib
import Definitions.Def_Formalism_PieriBlockIdeals_MultiplicityZeroThickEmbedding
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeckeLFunctionIdealEulerProduct
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ParameterBounds
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_WorkedExample

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.WorkedExample
open Formalism.CohomologicalDescent
namespace Formalism.CohomologicalDescent.WorkedExample
theorem _root_.solution : ReflIdentity := by
  intro n i μ
  constructor <;> push_cast <;> ring
end Formalism.CohomologicalDescent.WorkedExample
