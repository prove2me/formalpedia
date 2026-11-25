-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LBr2.twist_primitive
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:14:38.720482+00:00
-- url     : https://prove2.me/submissions/9a7752c5-a21d-4037-b982-5dcbcf0f1eab

import Definitions.Def_Formalism_SizeWindowBrackets_SmoothedRemainderRealIntegralFormula
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_GaloisMapComplexConjugation
import Definitions.Def_Formalism_LandauZeroFreeBounds_SiegelWalfiszAPOfSiegelLower
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_PrimeCongruenceConditions
import Theorems.Thm_Formalism_LFunctionChainParameters_LBr2_qc_prim
import Theorems.Thm_Formalism_LFunctionChainParameters_LBr2_qc_sq
import Theorems.Thm_Formalism_LFunctionChainParameters_LBr2_prim_mul
import Theorems.Thm_Formalism_LFunctionChainParameters_LBr2_chi_eight_sq
import Theorems.Thm_Formalism_LFunctionChainParameters_LBr2_chi_eight_primitive

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Filter Topology ArithmeticFunction DirichletCharacter
noncomputable section
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.LBr2
open Formalism Formalism.D5 Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LHost Formalism.LFunctionChainParameters.LErr Formalism.LFunctionChainParameters.LChain
  Formalism.LFunctionChainParameters.LChain2
namespace Formalism.LFunctionChainParameters.LBr2
theorem _root_.solution : TwPrimitive := by
  refine ⟨⟨chi_eight_primitive, chi_eight_sq⟩, ?_⟩
  intro t θ q _ hθ h2 hco
  have hq : q.Prime := Fact.out
  have ht : t ≠ 0 := by
    rintro rfl
    rw [Nat.coprime_zero_right] at hco
    exact hq.one_lt.ne' hco
  have : NeZero t := ⟨ht⟩
  have hp : (tw θ q).IsPrimitive :=
    prim_mul _ _ hco.symm rfl θ (qc q) hθ (qc_prim q h2)
  refine ⟨hp, ?_, ?_⟩
  · intro h1
    rw [isPrimitive_def, h1, conductor_one] at hp
    have h3 : 2 ≤ q := hq.two_le
    have h4 : 1 ≤ t := Nat.pos_of_ne_zero ht
    nlinarith
  · intro hs
    rw [tw, mul_pow, ← map_pow, ← map_pow, hs, qc_sq, map_one, map_one, one_mul]
end Formalism.LFunctionChainParameters.LBr2
