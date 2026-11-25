-- Prove2me | solution 1 for Formalism.G0.tops_choice_part_b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:54:12.896373+00:00
-- url     : https://prove2.me/submissions/c5701adf-950a-4b17-94cc-84f11a450a83

import Definitions.Def_Formalism_SubspaceCounting_TopsChoiceSecondBound
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_TopsChoicePartB
import Theorems.Thm_Formalism_G0_TopsWeightFunctionBounds_main

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
open Formalism Formalism.G0
namespace Formalism.G0
theorem _root_.solution : TopsChoiceSecondBound := TopsWeightFunctionBounds.main
end Formalism.G0
