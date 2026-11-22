-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.characterSumData.natCard_eq_filter
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:57:54.726281+00:00
-- url     : https://prove2.me/submissions/3d4a8318-816d-4ce6-99ad-0044ab97dc60

import Definitions.Def_Formalism_SizeWindowBrackets_FirstPrimeNeSecondPrime
import Definitions.Def_Formalism_ThickAverageLoss_ThickAverageProofs_Balance
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_StronglyIrreducible

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
open PB
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
namespace Formalism.LFunctionChainParameters.characterSumData
theorem _root_.solution (I : AddSubgroup (E0 × H)) [DecidablePred (fun x => x ∈ I)] :
    Nat.card I = (univ.filter (fun x => x ∈ I)).card := by
  first
  | (rw [Nat.card_eq_fintype_card]; exact Fintype.card_subtype _)
  | (rw [Nat.card_eq_fintype_card]; convert Fintype.card_subtype (fun x => x ∈ I))
  | simp [Nat.card_eq_fintype_card, Fintype.card_subtype]
end Formalism.LFunctionChainParameters.characterSumData
