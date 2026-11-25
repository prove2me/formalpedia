-- Prove2me | solution 1 for Formalism.CohomologicalDescent.WorkedExample.flip_sets_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:27:29.406274+00:00
-- url     : https://prove2.me/submissions/9a303c1e-d41b-46db-83b7-48235e6ecef2

import Mathlib
import Definitions.Def_Formalism_PieriBlockIdeals_MultiplicityZeroThickEmbedding
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeckeLFunctionIdealEulerProduct
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ParameterBounds
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_WorkedExample
import Theorems.Thm_Formalism_CohomologicalDescent_WorkedExample_image_Icc_neg_shift
import Theorems.Thm_Formalism_CohomologicalDescent_WorkedExample_sub_modEq_sub_iff

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
theorem _root_.solution : FlipSets := by
  intro l b h t κ
  refine ⟨?_, ?_, fun x u => sub_modEq_sub_iff l h x u⟩
  · rw [image_Icc_neg_shift]
    congr 1 <;> ring
  · rw [image_Icc_neg_shift]
    congr 1 <;> ring
end Formalism.CohomologicalDescent.WorkedExample
