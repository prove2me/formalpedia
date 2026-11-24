-- Prove2me | solution 1 for Formalism.CohomologicalDescent.UnitNormBounds.counts_cloud_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:16:11.384849+00:00
-- url     : https://prove2.me/submissions/8b9fecb5-e979-49f7-a730-8bf50bf581a0

import Definitions.Def_Formalism_PieriBlockIdeals_FactorialValuationSum
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LabelSumNeedsLeFalse
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_DividedPowerZeroZeroVector
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LastGradedImpliesOneBlock
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_UnitNormBounds
import Theorems.Thm_Formalism_CohomologicalDescent_UnitNormBounds_card_filter_rev_lt_le
import Theorems.Thm_Formalism_CohomologicalDescent_LD_ld_boxes_le


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.UnitNormBounds
open Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LD
namespace Formalism.CohomologicalDescent.UnitNormBounds
theorem _root_.solution : CountsCloud := by
  intro k j t w M i lam tau htau ct
  constructor
  · exact card_filter_rev_lt_le k j _
  · refine le_trans ?_ (ld_boxes_le t (M - w) i (k + j) (dual M lam) tau htau (cont t w M ct))
    unfold cloudBoxes boxesOfContent
    refine Finset.card_le_card ?_
    intro b hb
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hb).2.2⟩
end Formalism.CohomologicalDescent.UnitNormBounds
