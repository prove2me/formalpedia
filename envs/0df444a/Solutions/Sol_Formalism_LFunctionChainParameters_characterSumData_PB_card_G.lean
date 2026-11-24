-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.characterSumData.PB.card_G
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:28:06.949689+00:00
-- url     : https://prove2.me/submissions/815b8c0d-3b34-4150-ad44-51f45a2e6484

import Definitions.Def_Formalism_SizeWindowBrackets_FirstPrimeNeSecondPrime
import Definitions.Def_Formalism_ThickAverageLoss_ThickAverageProofs_Balance
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_StronglyIrreducible
import Theorems.Thm_Formalism_LFunctionChainParameters_characterSumData_PB_card_notPhi

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
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.characterSumData
open Formalism Formalism.D5
open Formalism.LFunctionChainParameters.characterSumData.PB
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
namespace Formalism.LFunctionChainParameters.characterSumData.PB
theorem _root_.solution : (Fintype.card (E0 × H) : ℂ) = 2 * ((PhiSet (H := H)).card : ℂ) := by
  have hN : Fintype.card (E0 × H) = 2 * (PhiSet (H := H)).card := by
    first
    | rw [← Finset.card_univ, ← Finset.filter_card_add_filter_neg_card_eq_card (p := InPhi), card_notPhi]
    | rw [← Finset.card_univ, ← Finset.card_filter_add_card_filter_not (p := InPhi), card_notPhi]
    simp only [PhiSet]
    ring
  exact_mod_cast hN
end Formalism.LFunctionChainParameters.characterSumData.PB
