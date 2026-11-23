-- Prove2me | solution 1 for Formalism.D5.trivH_chpsC
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:06:56.082285+00:00
-- url     : https://prove2.me/submissions/93317b64-39db-47bf-84fe-7a6226da67bc

import Definitions.Def_Formalism_ThickAverageLoss_ParametersAveragedDifferenceBound
import Definitions.Def_Formalism_ThickAverageLoss_PartnersToFactorsAt
import Definitions.Def_Formalism_ThickAverageLoss_ThickAverageProofs_ThickAverage
import Theorems.Thm_Formalism_D5_signZModTwo_zero

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
theorem _root_.solution (Hs : CycHost H) : TrivH Hs.chpsC := by
  unfold TrivH
  intro h
  simp [Hs.chpsC_apply, signZModTwo_zero]
end Formalism.D5
