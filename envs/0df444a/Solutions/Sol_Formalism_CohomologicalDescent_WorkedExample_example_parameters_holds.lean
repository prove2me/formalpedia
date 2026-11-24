-- Prove2me | solution 1 for Formalism.CohomologicalDescent.WorkedExample.example_parameters_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:03:25.882809+00:00
-- url     : https://prove2.me/submissions/96288d05-d982-48c5-86d3-ff7c85a6df27

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
theorem _root_.solution : WeightAddRhoEqParameter := by
  intro p q' t v β e i
  unfold twistedSequenceWeight exampleParameterVector rho
  induction i using Fin.addCases with
  | left i =>
    induction i using Fin.addCases with
    | left i =>
      simp only [Fin.append_left, aPlus, Fin.val_castAdd]
      push_cast
      ring
    | right a =>
      simp only [Fin.append_left, Fin.append_right, Fin.val_castAdd, Fin.val_natAdd]
      push_cast
      ring
  | right c =>
    simp only [Fin.append_right, aMinus, Fin.rev_rev, Fin.val_natAdd]
    push_cast
    ring
end Formalism.CohomologicalDescent.WorkedExample
