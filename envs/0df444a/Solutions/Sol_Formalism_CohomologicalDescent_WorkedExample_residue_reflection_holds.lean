-- Prove2me | solution 1 for Formalism.CohomologicalDescent.WorkedExample.residue_reflection_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:24:32.94168+00:00
-- url     : https://prove2.me/submissions/4dba1615-1b29-4340-a882-2cbd06fc6cfa

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
theorem _root_.solution : ResidueFlip := by
  intro l N U U' h H
  have H2 := congrArg (Multiset.map (fun z : ZMod l => (h : ZMod l) - z)) H
  simpa [Multiset.map_map, Function.comp_def, Int.cast_sub] using H2
end Formalism.CohomologicalDescent.WorkedExample
