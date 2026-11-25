-- Prove2me | solution 1 for Formalism.CohomologicalDescent.WorkedExample.tail_line_needs_f_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:24:34.439458+00:00
-- url     : https://prove2.me/submissions/6869cb28-5e71-423e-9b5c-bf631365ccc9

import Mathlib
import Definitions.Def_Formalism_PieriBlockIdeals_MultiplicityZeroThickEmbedding
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeckeLFunctionIdealEulerProduct
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ParameterBounds
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_WorkedExample
import Theorems.Thm_Formalism_CohomologicalDescent_WorkedExample_example_params_satisfy_hyp
import Theorems.Thm_Formalism_CohomologicalDescent_WorkedExample_example_params_large
import Theorems.Thm_P2M_Formalism_CohomologicalDescent_LogSmallConstantBounds_b_pos__c78f2de8288c


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
theorem _root_.solution : ParameterQuotientBoundFailsAtFEqOne := by
  refine ⟨exampleParamsAlt, example_params_satisfy_hyp, example_params_large, rfl, by norm_num [exampleParamsAlt], ?_⟩
  have hp : 0 < exampleParamsAlt.b := LogSmallConstantBounds.b_pos' _
  show ((1 : ℕ) : ℝ) * exampleParamsAlt.b * 60 < 12 * 60 * exampleParamsAlt.b / (((6 : ℕ) : ℝ) * ((1 : ℕ) : ℝ) * ((1 : ℕ) : ℝ) ^ 3)
  rw [lt_div_iff₀ (by norm_num)]
  push_cast
  linarith
end Formalism.CohomologicalDescent.WorkedExample
