-- Prove2me | solution 1 for Deduction.CharacterBalance.cardI
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:37:04.105297+00:00
-- url     : https://prove2.me/submissions/0c5e3cbe-4ac0-4b95-b48d-714a3437d056

import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_SplitInertia
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_StronglyIrreducible
import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauTheorems_ChBalance
import Theorems.Thm_Formalism_LFunctionChainParameters_characterSumData_natCard_eq_filter


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
open Deduction
open Deduction.CH Formalism Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LErr Formalism.LFunctionChainParameters.LChain
open Deduction.CharacterBalance
open ArithmeticFunction Formalism.LFunctionChainParameters.characterSumData.PB
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
namespace Deduction.CharacterBalance
theorem _root_.solution (D : ArithData H) {S0 : Finset ℕ} (hD : HostFactsS D S0) : (Nat.card (D.inertia D.d) : ℂ) = 2 := by
  classical
  rw [natCard_eq_filter]
  have : univ.filter (fun x => x ∈ D.inertia D.d) = ({0, sgc0} : Finset (E0 × H)) := by
    ext x; simp [hD.inertia_d]
  rw [this, Finset.card_pair (by unfold sgc0; intro h; have := congrArg (fun x : E0 × H => x.1.1) h; simp at this)]
  norm_num
end Deduction.CharacterBalance
