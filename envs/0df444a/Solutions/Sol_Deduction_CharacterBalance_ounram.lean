-- Prove2me | solution 1 for Deduction.CharacterBalance.ounram
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:56:35.820882+00:00
-- url     : https://prove2.me/submissions/7d44ffa3-93bb-44e4-b5ae-41e3f9bcd8fa

import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_SplitInertia
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_StronglyIrreducible
import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauTheorems_ChBalance
import Theorems.Thm_Formalism_LFunctionChainParameters_characterSumData_orthogonality_ramified


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
theorem _root_.solution (D : ArithData H) {S0 : Finset ℕ} (hD : HostFactsS D S0) (p i : ℕ) (hp : p.Prime) (h2 : p ∉ S0)
    (hd : p ≠ D.d) (hi : 1 ≤ i) (g : E0 × H) :
    (1 / ((PhiSet (H := H)).card : ℂ)) * ∑ ψ : AddChar (E0 × H) ℂ,
        starRingEnd ℂ (ψ g) * primVal D ψ (p ^ i)
      = if i • D.frob p = g then 2 else 0 := by
  classical
  have := orthogonality_ramified D p i hp hi g
  rw [this, hD.unram p hp h2 hd]
  by_cases he : i • D.frob p = g
  · rw [if_pos he, if_pos (by rw [he, sub_self]; exact AddSubgroup.zero_mem _), AddSubgroup.card_bot]
    norm_num
  · rw [if_neg he, if_neg (by rw [AddSubgroup.mem_bot, sub_eq_zero]; exact fun e => he e.symm)]
end Deduction.CharacterBalance
