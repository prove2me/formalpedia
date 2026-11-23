-- Prove2me | solution 1 for Formalism.D5.Bal.card_G_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:59:20.596302+00:00
-- url     : https://prove2.me/submissions/ed671d3c-b9e4-4917-b5fd-f41addf39285

import Definitions.Def_Formalism_ThickAverageLoss_PartnersToFactorsAt
import Definitions.Def_Formalism_ThickAverageLoss_ThickAverageProofs_Balance
import Theorems.Thm_Formalism_D5_Bal_inPhi_add_topPl
import Theorems.Thm_Formalism_D5_Bal_card_S

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset ArithmeticFunction
noncomputable section
open Formalism Formalism.D5
open Formalism Formalism.CMTypeGaloisData Formalism.WT Formalism.WeightedSieveThreeParameter
open Formalism.D5.Bal
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
namespace Formalism.D5.Bal
theorem _root_.solution : (Fintype.card (E0 × H) : ℂ) = 2 * ((PhiSet (H := H)).card : ℂ) := by
  have h1 : (univ.filter (fun g : E0 × H => InPhi g)).card
      + (univ.filter (fun g : E0 × H => ¬ InPhi g)).card = Fintype.card (E0 × H) := by
    rw [Finset.card_eq_sum_ones, Finset.card_eq_sum_ones, ← Finset.card_univ, Finset.card_eq_sum_ones]
    exact Finset.sum_filter_add_sum_filter_not _ _ _
  have h2 : (univ.filter (fun g : E0 × H => ¬ InPhi g)).card = (PhiSet (H := H)).card := by
    rw [← card_S (H := H) 0]
    congr 1
    apply Finset.filter_congr
    intro g _
    rw [inPhi_add_topPl]
  have h3 : univ.filter (fun g : E0 × H => InPhi g) = PhiSet (H := H) := PhiSet.eq_1.symm
  rw [← h1, h2, h3]
  push_cast
  ring
end Formalism.D5.Bal
