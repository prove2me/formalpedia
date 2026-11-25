-- Prove2me | solution 1 for Formalism.ResultantValuation.powSubOneValuation
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:20:03.605804+00:00
-- url     : https://prove2.me/submissions/bb5ed0c3-c2df-4ee9-b7a9-91734722bc93

import Mathlib
import Definitions.Def_Formalism_ResultantValuation_WindowValuation
import Definitions.Def_Formalism_ResultantValuation_ResultantAdjugateProofs_Window
import Theorems.Thm_Formalism_ResultantValuation_lte_unit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.ResultantValuation
namespace Formalism.ResultantValuation
theorem _root_.solution : LTEUnit := by
  intro l _ hl2 u hu i hi
  exact lte_unit l hl2 u hu i hi
end Formalism.ResultantValuation
