-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LD.blockDual
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:25:44.238304+00:00
-- url     : https://prove2.me/submissions/c32dfaf9-6e67-4248-b17c-d01dc89ad567

import Definitions.Def_Formalism_PieriBlockIdeals_LastGradedOfGradedAlone
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LastGradedImpliesOneBlock
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightShiftEqDetMul
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LEhwLemmas
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightProdLeadingMinors
import Theorems.Thm_Formalism_CohomologicalDescent_LD_rev_cast_castAdd_eq_natAdd
import Theorems.Thm_Formalism_CohomologicalDescent_LD_rev_cast_natAdd_eq_castAdd
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open MvPolynomial
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LD
open Formalism.GradedWeylDivisibility Formalism.CohomologicalDescent.LA
namespace Formalism.CohomologicalDescent.LD
theorem _root_.solution : BlockDual := by
  intro p q w M κ
  funext a
  refine Fin.addCases (fun a' => ?_) (fun a' => ?_) a
  · simp only [dualWt, blockWt, blockWtLast, rev_cast_castAdd_eq_natAdd, Fin.append_left, Fin.append_right]
  · simp only [dualWt, blockWt, blockWtLast, rev_cast_natAdd_eq_castAdd, Fin.append_left, Fin.append_right]
end Formalism.CohomologicalDescent.LD
