-- Prove2me | solution 1 for Formalism.D5.thick_inj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:20:40.673512+00:00
-- url     : https://prove2.me/submissions/4fac72bf-b610-4bca-9d7b-f8e0858c625c

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
theorem _root_.solution (u0 t : H) :
    Set.InjOn (fun s => ((((1 : ZMod 2), (0 : ZMod 2)), s + u0 - t) : E0 × H)) Set.univ := by
  intro x _ y _ hxy
  simpa using hxy
end Formalism.D5
