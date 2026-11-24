-- Prove2me | solution 1 for Formalism.CohomologicalDescent.WorkedExample.example_run_entry_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:05:06.610618+00:00
-- url     : https://prove2.me/submissions/ce6ced2a-58ca-4409-ae62-9784c72ef297

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
theorem _root_.solution (p q' t : ℕ) (v : Fin p → ℝ) (β : Fin q' → ℝ) (e : ℝ) (a : Fin t) :
    exampleParameterVector p q' t v β e (Fin.castAdd q' (Fin.natAdd p a)) =
      -e + ((t : ℝ) - 1) / 2 - ((a : ℕ) : ℝ) := by
  simp only [exampleParameterVector, Fin.append_left, Fin.append_right]
  ring
end Formalism.CohomologicalDescent.WorkedExample
