-- Prove2me | solution 1 for Formalism.D5.zmod_two_cases_bis
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:50:40.888442+00:00
-- url     : https://prove2.me/submissions/31718480-8bb3-4920-8d00-e89b9f6a6199

import Definitions.Def_Formalism_ThickAverageLoss_ParametersAveragedDifferenceBound
import Definitions.Def_Formalism_ThickAverageLoss_PartnersToFactorsAt
import Definitions.Def_Formalism_ThickAverageLoss_ThickAverageProofs_ThickAverage

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.D5
open Formalism Formalism.CMTypeGaloisData Formalism.WT Formalism.WeightedSieveThreeParameter
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
namespace Formalism.D5
theorem _root_.solution (x : ZMod 2) : x = 0 ∨ x = 1 := by
  first
    | (revert x; decide)
    | (fin_cases x <;> simp)
end Formalism.D5
