-- Prove2me | solution 1 for Formalism.CohomologicalDescent.WorkedExample.example_b_div_lstar_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:16:14.4185+00:00
-- url     : https://prove2.me/submissions/c008478f-9039-41bc-8b79-c9ec279fd70f

import Mathlib
import Definitions.Def_Formalism_PieriBlockIdeals_MultiplicityZeroThickEmbedding
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeckeLFunctionIdealEulerProduct
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ParameterBounds
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_WorkedExample
import Theorems.Thm_Formalism_CohomologicalDescent_WorkedExample_two_pow_sixty_le_example_b
import Theorems.Thm_Formalism_CohomologicalDescent_WorkedExample_example_lstar_eq_b_div

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
theorem _root_.solution : exampleParamsAlt.b / exampleParamsAlt.lstar = 1814470 := by
  have := two_pow_sixty_le_example_b
  have hp : 0 < exampleParamsAlt.b := by linarith [show (0 : ℝ) < 2 ^ 60 by norm_num]
  rw [example_lstar_eq_b_div]; field_simp
end Formalism.CohomologicalDescent.WorkedExample
