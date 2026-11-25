-- Prove2me | solution 1 for Formalism.CohomologicalDescent.WorkedExample.line_c_identity_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:24:29.403542+00:00
-- url     : https://prove2.me/submissions/3bfaaad7-c869-4328-bcec-b63b3372b36b

import Mathlib
import Definitions.Def_Formalism_PieriBlockIdeals_MultiplicityZeroThickEmbedding
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeckeLFunctionIdealEulerProduct
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ParameterBounds
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_WorkedExample
import Theorems.Thm_Formalism_CohomologicalDescent_LogSmallConstantBounds_b_div_lstar_pos
import Theorems.Thm_Formalism_CohomologicalDescent_LogSmallConstantBounds_two_mul_lstar_le_b
import Theorems.Thm_P2M_Formalism_CohomologicalDescent_LogSmallConstantBounds_eta_nonneg__1aa77f39dc77


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
theorem _root_.solution : LstarGapInequalities := by
  intro P H G
  have h1 := H.sum_lt
  have h2 := H.win_lt
  have h3 := H.b'_pos
  have h4 := LogSmallConstantBounds.b_div_lstar_pos H G
  have h5 := LogSmallConstantBounds.eta_nonneg' H
  have h6 := LogSmallConstantBounds.two_mul_lstar_le_b H G
  have e8 : 8 * P.b / P.lstar = 8 * (P.b / P.lstar) := mul_div_assoc _ _ _
  have e2 : 2 * P.b / P.lstar = 2 * (P.b / P.lstar) := mul_div_assoc _ _ _
  rw [e8] at h2
  rw [e2]
  refine ⟨by linarith, by linarith, by linarith, h6, by linarith⟩
end Formalism.CohomologicalDescent.WorkedExample
