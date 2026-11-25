-- Prove2me | solution 1 for Formalism.CohomologicalDescent.WorkedExample.example_weight_zero_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:27:26.373794+00:00
-- url     : https://prove2.me/submissions/f1f47972-d7fa-4e9e-960c-e2c848bca286

import Mathlib
import Definitions.Def_Formalism_PieriBlockIdeals_MultiplicityZeroThickEmbedding
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeckeLFunctionIdealEulerProduct
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ParameterBounds
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_WorkedExample
import Theorems.Thm_Formalism_CohomologicalDescent_WorkedExample_example_shape_holds
import Theorems.Thm_Formalism_CohomologicalDescent_LogSmallConstantBounds_noWindowResidue_holds


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
theorem _root_.solution : MultiplicityZeroThickEmbedding := by
  intro P H G l hl hlJ kc j q' cloud bu bd e c σ z bot hσ hcl hbu hbd hz hbot hcase
  exact LogSmallConstantBounds.noWindowResidue_holds P H G l hl hlJ _ bot c e σ
    (example_shape_holds P kc j q' cloud bu bd e c σ z bot hσ hcl hbu hbd hz hbot) hcase
end Formalism.CohomologicalDescent.WorkedExample
