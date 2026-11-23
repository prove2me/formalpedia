-- Prove2me | solution 1 for Formalism.A.smith_form_exists
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:17:15.080105+00:00
-- url     : https://prove2.me/submissions/05a1db26-53f9-4c88-8ea1-bccabadf55ba

import Definitions.Def_Formalism_SmithDeterminants_DefsDVR
import Definitions.Def_Formalism_SmithDeterminants_DivisibilityChains_SmithExists
import Theorems.Thm_Formalism_A_nonempty_smith_normal_form

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.A
open Module
namespace Formalism.A
theorem _root_.solution : SmithExists := by
  unfold SmithExists
  intro R M _ _ _ _ _ _ _ y
  exact nonempty_smith_normal_form y
end Formalism.A
