-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LBr2.chi_eight_primitive
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:40:28.875807+00:00
-- url     : https://prove2.me/submissions/0988ddb4-9b61-4a82-9415-6aead7f0b994

import Definitions.Def_Formalism_SizeWindowBrackets_SmoothedRemainderRealIntegralFormula
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_GaloisMapComplexConjugation
import Definitions.Def_Formalism_LandauZeroFreeBounds_SiegelWalfiszAPOfSiegelLower
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_PrimeCongruenceConditions

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
theorem _root_.solution : chi8.IsPrimitive := by
  rw [isPrimitive_def]
  by_contra hne
  have hd := conductor_dvd_level chi8
  have h4 : chi8.conductor ∣ 4 := by
    have hle : chi8.conductor ≤ 8 := Nat.le_of_dvd (by norm_num) hd
    generalize chi8.conductor = k at *
    interval_cases k <;> omega
  obtain ⟨hd4, χ₀, h0⟩ : chi8.FactorsThrough 4 :=
    (mem_conductorSet_iff_conductor_dvd _ (by norm_num)).2 h4
  have h5 : changeLevel hd4 χ₀ ((5 : ℤ) : ZMod 8) = χ₀ ((5 : ℤ) : ZMod 4) :=
    changeLevel_eq_cast_of_dvd' χ₀ hd4 (by
      rw [Int.isCoprime_iff_gcd_eq_one]; decide)
  rw [← h0] at h5
  have h6 : ((5 : ℤ) : ZMod 4) = 1 := by decide
  have h7 : ZMod.χ₈ ((5 : ℤ) : ZMod 8) = -1 := by decide
  rw [h6, map_one, chi8, MulChar.ringHomComp_apply, h7] at h5
  norm_num at h5
end Formalism.LFunctionChainParameters.LBr2
