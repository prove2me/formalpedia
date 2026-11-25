-- Prove2me | solution 1 for Formalism.CohomologicalDescent.WorkedExample.example_run_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:23:12.488511+00:00
-- url     : https://prove2.me/submissions/e32c3402-9505-4711-aba2-3bd46cafd1f4

import Mathlib
import Definitions.Def_Formalism_PieriBlockIdeals_MultiplicityZeroThickEmbedding
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeckeLFunctionIdealEulerProduct
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ParameterBounds
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_WorkedExample
import Theorems.Thm_Formalism_CohomologicalDescent_WorkedExample_example_run_entry_eq

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
theorem _root_.solution : ParameterSequenceCentred := by
  intro p q' t v β e a
  refine ⟨example_run_entry_eq p q' t v β e a, ?_⟩
  rw [example_run_entry_eq, example_run_entry_eq, Fin.val_rev]
  have ha : (a : ℕ) + 1 ≤ t := a.isLt
  rw [Nat.cast_sub ha]
  push_cast
  ring
end Formalism.CohomologicalDescent.WorkedExample
