-- Prove2me | solution 1 for Formalism.CohomologicalDescent.WorkedExample.example_lstar_eq_b_div
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:05:04.44766+00:00
-- url     : https://prove2.me/submissions/6a044ab6-cb0a-4137-9609-f05755c04a6c

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
theorem _root_.solution : exampleParamsAlt.lstar = exampleParamsAlt.b / 1814470 := by
  simp only [LogSmallConstantBounds.Par.lstar, LogSmallConstantBounds.Par.N, exampleParamsAlt]; norm_num
end Formalism.CohomologicalDescent.WorkedExample
