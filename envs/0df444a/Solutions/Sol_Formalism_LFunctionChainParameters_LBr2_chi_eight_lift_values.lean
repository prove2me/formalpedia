-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LBr2.chi_eight_lift_values
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T02:26:47.61405+00:00
-- url     : https://prove2.me/submissions/46bda6e7-be49-4cb2-b02b-abbb68955f19

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
variable {e q d : ℕ} [Fact q.Prime] [Fact d.Prime]
namespace Formalism.LFunctionChainParameters.LBr2
theorem _root_.solution (e : ℕ) (h8 : 8 ∣ 2 ^ (e + 2)) :
    changeLevel h8 chi8 ((-1 : (ZMod (2 ^ (e + 2)))ˣ) : ZMod (2 ^ (e + 2))) = 1 ∧
    changeLevel h8 chi8 ((TwoAdicCyclotomicDecomposition.u5 (e + 2) : (ZMod (2 ^ (e + 2)))ˣ) : ZMod (2 ^ (e + 2))) = -1 := by
  constructor
  · have h := changeLevel_eq_cast_of_dvd' chi8 h8 (a := -1) (by
      exact (isCoprime_one_left).neg_left)
    have e1 : (((-1 : ℤ)) : ZMod (2 ^ (e + 2))) = ((-1 : (ZMod (2 ^ (e + 2)))ˣ) : ZMod (2 ^ (e + 2))) := by
      simp
    rw [e1] at h
    rw [h, chi8, MulChar.ringHomComp_apply]
    have : ZMod.χ₈ ((-1 : ℤ) : ZMod 8) = 1 := by decide
    rw [this]
    simp
  · have h := changeLevel_eq_cast_of_dvd' chi8 h8 (a := 5) (by
      push_cast
      apply IsCoprime.pow_right
      rw [Int.isCoprime_iff_gcd_eq_one]
      decide)
    have e1 : (((5 : ℤ)) : ZMod (2 ^ (e + 2))) = ((TwoAdicCyclotomicDecomposition.u5 (e + 2) : (ZMod (2 ^ (e + 2)))ˣ) : ZMod (2 ^ (e + 2))) := by
      unfold TwoAdicCyclotomicDecomposition.u5
      rw [ZMod.coe_unitOfCoprime]
      simp
    rw [e1] at h
    rw [h, chi8, MulChar.ringHomComp_apply]
    have : ZMod.χ₈ ((5 : ℤ) : ZMod 8) = -1 := by decide
    rw [this]
    simp
end Formalism.LFunctionChainParameters.LBr2
