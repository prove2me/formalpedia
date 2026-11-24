-- Prove2me | solution 1 for Formalism.CohomologicalDescent.WorkedExample.two_pow_sixty_le_example_b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:04:51.614856+00:00
-- url     : https://prove2.me/submissions/9c67b31a-526d-4732-9af6-faa18f8100b7

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
theorem _root_.solution : (2 : ℝ) ^ 60 ≤ exampleParamsAlt.b := by
  show (2 : ℝ) ^ 60 ≤ Real.exp 60
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  calc (2 : ℝ) ^ 60 ≤ (Real.exp 1) ^ 60 := by gcongr
    _ = Real.exp 60 := by rw [← Real.exp_nat_mul]; norm_num
end Formalism.CohomologicalDescent.WorkedExample
