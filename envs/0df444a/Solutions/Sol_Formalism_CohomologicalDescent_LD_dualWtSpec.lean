-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LD.dualWtSpec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:17:13.661914+00:00
-- url     : https://prove2.me/submissions/175ad9dd-c13a-4f90-bd54-7c2f81fa8c21

import Definitions.Def_Formalism_PieriBlockIdeals_LastGradedOfGradedAlone
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LastGradedImpliesOneBlock
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightShiftEqDetMul
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LEhwLemmas
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightProdLeadingMinors
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
theorem _root_.solution : DualWtSpec := by
  intro r M κ
  refine ⟨fun h => ?_, fun a => Nat.sub_le _ _, fun h a b hab => ?_⟩
  · funext a
    simp only [dualWt, Fin.rev_rev]
    have := h a
    omega
  · exact Nat.sub_le_sub_left (h (Fin.rev_le_rev.mpr hab)) M
end Formalism.CohomologicalDescent.LD
