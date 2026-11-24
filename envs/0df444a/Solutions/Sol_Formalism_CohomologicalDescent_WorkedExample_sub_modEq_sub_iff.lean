-- Prove2me | solution 1 for Formalism.CohomologicalDescent.WorkedExample.sub_modEq_sub_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:03:30.022465+00:00
-- url     : https://prove2.me/submissions/743568b2-bdf4-408e-b2fa-284f3c2696bf

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
theorem _root_.solution (l : ℕ) (h x u : ℤ) :
    h - x ≡ h - u [ZMOD (l : ℤ)] ↔ x ≡ u [ZMOD (l : ℤ)] := by
  rw [Int.modEq_iff_dvd, Int.modEq_iff_dvd, show h - u - (h - x) = -(u - x) by ring, dvd_neg]
end Formalism.CohomologicalDescent.WorkedExample
