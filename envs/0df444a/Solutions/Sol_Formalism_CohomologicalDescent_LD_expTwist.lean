-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LD.expTwist
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:56:55.473307+00:00
-- url     : https://prove2.me/submissions/2837ba3d-2c3a-4b0f-8a2b-9883cdc25b05

import Definitions.Def_Formalism_PieriBlockIdeals_LastGradedOfGradedAlone
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LastGradedImpliesOneBlock
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightShiftEqDetMul
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LEhwLemmas
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightProdLeadingMinors
import Theorems.Thm_Formalism_CohomologicalDescent_LD_exp_le_shift_by_one_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LD
open Formalism.GradedWeylDivisibility Formalism.CohomologicalDescent.LA
namespace Formalism.CohomologicalDescent.LD
theorem _root_.solution : ExpTwist := by
  intro l r c ν μ e hν
  induction c with
  | zero => exact Iff.rfl
  | succ c ih =>
    have hν' : Antitone (fun a => ν a + c) := fun a b hab => Nat.add_le_add_right (hν hab) c
    exact (exp_le_shift_by_one_iff l r (fun a => ν a + c) (fun a => μ a + c) e hν').trans ih
end Formalism.CohomologicalDescent.LD
