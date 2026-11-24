-- Prove2me | solution 1 for Formalism.CohomologicalDescent.WorkedExample.example_params_large
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:23:48.489785+00:00
-- url     : https://prove2.me/submissions/1b4c6123-46df-4d7c-bfaa-73cf9e986419

import Mathlib
import Definitions.Def_Formalism_PieriBlockIdeals_MultiplicityZeroThickEmbedding
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeckeLFunctionIdealEulerProduct
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ParameterBounds
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_WorkedExample
import Theorems.Thm_Formalism_CohomologicalDescent_WorkedExample_two_pow_sixty_le_example_b
import Theorems.Thm_Formalism_CohomologicalDescent_WorkedExample_example_b_div_lstar_eq

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
theorem _root_.solution : exampleParamsAlt.Large := by
  have hb := two_pow_sixty_le_example_b
  have e := example_b_div_lstar_eq
  have e2 : 2 * exampleParamsAlt.b / exampleParamsAlt.lstar = 2 * 1814470 := by rw [mul_div_assoc, e]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · norm_num [exampleParamsAlt]
  · norm_num [exampleParamsAlt] at hb ⊢; linarith
  · norm_num [exampleParamsAlt] at hb ⊢; linarith
  · rw [e2]; norm_num [exampleParamsAlt, LogSmallConstantBounds.Par.w'']
  · norm_num [exampleParamsAlt]
end Formalism.CohomologicalDescent.WorkedExample
