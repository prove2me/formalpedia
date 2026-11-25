-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LD.expDualOfLattices
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:46:25.365649+00:00
-- url     : https://prove2.me/submissions/18ec2d3b-37ee-4633-b1d0-09f4b41417c6

import Definitions.Def_Formalism_PieriBlockIdeals_LastGradedOfGradedAlone
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LastGradedImpliesOneBlock
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightShiftEqDetMul
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LEhwLemmas
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightProdLeadingMinors
import Theorems.Thm_Formalism_CohomologicalDescent_LD_dualWtSpec
import Theorems.Thm_Formalism_CohomologicalDescent_LD_exp_le_of_dual_exp_le

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
theorem _root_.solution : ExpDualOfLattices := by
  intro hN hW hT hC l r M ν μ e hl hν hνM hμM
  constructor
  · intro h
    refine exp_le_of_dual_exp_le hN hW hT hC l r M (dualWt M ν) (dualWt M μ) e hl ((dualWtSpec r M ν).2.2 hν)
      (dualWtSpec r M ν).2.1 (dualWtSpec r M μ).2.1 ?_
    rw [(dualWtSpec r M ν).1 hνM, (dualWtSpec r M μ).1 hμM]
    exact h
  · exact exp_le_of_dual_exp_le hN hW hT hC l r M ν μ e hl hν hνM hμM
end Formalism.CohomologicalDescent.LD
