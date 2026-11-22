-- Prove2me | solution 1 for Formalism.D5.zmod_two_one_add_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:48:56.087802+00:00
-- url     : https://prove2.me/submissions/a2a3adb3-6492-40d8-80f9-33b1ac823889

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
theorem _root_.solution : (1 : ZMod 2) + 1 = 0 := by
  decide
end Formalism.D5
