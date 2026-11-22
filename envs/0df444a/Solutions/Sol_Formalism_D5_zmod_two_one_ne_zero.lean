-- Prove2me | solution 1 for Formalism.D5.zmod_two_one_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:49:19.100404+00:00
-- url     : https://prove2.me/submissions/70bc2fac-2e63-4b24-ac04-3285d40f7a76

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
theorem _root_.solution : (1 : ZMod 2) ≠ 0 := by
  decide
end Formalism.D5
