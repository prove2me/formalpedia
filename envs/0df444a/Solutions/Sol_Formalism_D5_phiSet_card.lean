-- Prove2me | solution 1 for Formalism.D5.phiSet_card
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:18:50.310392+00:00
-- url     : https://prove2.me/submissions/d40ef043-1db3-4c24-b284-dd2be7d1e60f

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
theorem _root_.solution : (PhiSet (H := H)).card = 2 * Fintype.card H := by
  have h1 : PhiSet (H := H) =
      (Finset.univ.filter (fun e : E0 => e.1 = 0)) ×ˢ (Finset.univ : Finset H) := by
    ext ⟨⟨a, b⟩, h⟩
    simp [PhiSet, InPhi]
  have h2 : (Finset.univ.filter (fun e : E0 => e.1 = 0)).card = 2 := by
    first
      | decide
      | rfl
  rw [h1, Finset.card_product, h2, Finset.card_univ]
end Formalism.D5
