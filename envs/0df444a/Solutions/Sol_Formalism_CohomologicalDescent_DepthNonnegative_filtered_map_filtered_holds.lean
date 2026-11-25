-- Prove2me | solution 1 for Formalism.CohomologicalDescent.DepthNonnegative.filtered_map_filtered_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:20:10.889651+00:00
-- url     : https://prove2.me/submissions/8987dbdb-7aa6-4484-b353-98c30fb98268

import Definitions.Def_Formalism_PieriBlockIdeals_BlockIdealBound5Derived
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ProdInitialMinorsMemDetSpan
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_UnitNormBounds
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_JointCorollaryFiveBound
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LDbasisLemmas
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_FormsTensorLocalization
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_RegularCuspidalTrace
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_DepthNonnegative
import Theorems.Thm_Formalism_CohomologicalDescent_DepthNonnegative_filtered_extension_holds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct MvPolynomial
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.DepthNonnegative
open Formalism.UG Formalism.RankGapBounds.FormsTensorLocalization Formalism.GradedWeylDivisibility Formalism.CohomologicalDescent.LD Formalism.CohomologicalDescent.UnitNormBounds
open CategoryTheory CategoryTheory.Limits
namespace Formalism.CohomologicalDescent.DepthNonnegative
theorem _root_.solution : FilteredMapFiltered := by
  intro C D _ _ _ _ F _ _ _ P P' hP Y hY
  induction hY with
  | zero Y h => exact Filtered.zero _ (F.map_isZero h)
  | step S hS _ h3 ih => exact filtered_extension_holds D P' (S.map F) (hS.map_of_exact F) ih (hP _ h3)
end Formalism.CohomologicalDescent.DepthNonnegative
