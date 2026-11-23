-- Prove2me | solution 1 for Formalism.D5.productCharacter_second_basis
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:09:32.668885+00:00
-- url     : https://prove2.me/submissions/eae54697-1e0a-4ebe-a650-65a4b0cf7c71

import Definitions.Def_Formalism_ThickAverageLoss_ParametersAveragedDifferenceBound
import Definitions.Def_Formalism_ThickAverageLoss_PartnersToFactorsAt
import Definitions.Def_Formalism_ThickAverageLoss_ThickAverageProofs_ThickAverage
import Theorems.Thm_Formalism_D5_signZModTwo_zero
import Theorems.Thm_Formalism_D5_signZModTwo_one

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
theorem _root_.solution (Hs : CycHost H) : Hs.chpsC e01 = -1 := by
  simp [Hs.chpsC_apply, e01, signZModTwo_one, signZModTwo_zero]
end Formalism.D5
