-- Prove2me | solution 1 for Formalism.D5.sq_one_of_order2
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:09:33.164854+00:00
-- url     : https://prove2.me/submissions/4b4ced52-da2c-419a-9f11-0b74b44e4291

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
theorem _root_.solution (ψ : AddChar (E0 × H) ℂ) (g : E0 × H) (hg : g + g = 0) : ψ g * ψ g = 1 := by
  rw [← AddChar.map_add_eq_mul, hg, AddChar.map_zero_eq_one]
end Formalism.D5
