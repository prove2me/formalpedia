-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LChain.Model.hostFacts_DA
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:07:44.353924+00:00
-- url     : https://prove2.me/submissions/9a856491-38cc-4b43-9296-c018cc308538

import Definitions.Def_Formalism_SizeWindowBrackets_SChain
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_LevelOfCongruence
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_LipschitzWeightAndMinimum
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_SubThreeMulLogTwoLe
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_PChain

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
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.LChain
open Formalism Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LErr
open Formalism.LFunctionChainParameters.LChain.Model
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
namespace Formalism.LFunctionChainParameters.LChain.Model
theorem _root_.solution : HostFacts (DA (H := H)) where
  first_prime_prime := by show Nat.Prime 11; norm_num
  d_prime := by show Nat.Prime 7; norm_num
  first_prime_ne_two := by show (11 : ℕ) ≠ 2; norm_num
  d_ne_two := by show (7 : ℕ) ≠ 2; norm_num
  firstPrime_ne_secondPrime := by show (11 : ℕ) ≠ 7; norm_num
  unram := by
    intro p _ _ _ h7
    have h7' : p ≠ 7 := h7
    show (if p = 7 then Id else ⊥) = ⊥
    rw [if_neg h7']
  split_inertia := by
    intro p hp x hx
    have h7 : p ≠ 7 := by
      rcases hp with rfl | rfl
      · norm_num
      · show (11 : ℕ) ≠ 7; norm_num
    have hx' : x ∈ (if p = 7 then Id else (⊥ : AddSubgroup (E0 × H))) := hx
    rw [if_neg h7, AddSubgroup.mem_bot] at hx'
    subst hx'
    simp [InPhi]
  split_frob := by
    intro p _
    show InPhi (0 : E0 × H)
    simp [InPhi]
  inertia_d := by
    intro x
    show x ∈ (if (7 : ℕ) = 7 then Id else (⊥ : AddSubgroup (E0 × H))) ↔ _
    rw [if_pos rfl]
    exact Iff.rfl
end Formalism.LFunctionChainParameters.LChain.Model
