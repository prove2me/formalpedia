-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LBr2.thin_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:52:28.030183+00:00
-- url     : https://prove2.me/submissions/1ae961ea-4660-4231-ba14-e7f9b2af7def

import Definitions.Def_Formalism_SizeWindowBrackets_SmoothedRemainderRealIntegralFormula
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_GaloisMapComplexConjugation
import Definitions.Def_Formalism_LandauZeroFreeBounds_SiegelWalfiszAPOfSiegelLower
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_PrimeCongruenceConditions
import Theorems.Thm_Formalism_LFunctionChainParameters_LBr2_g_psi_at_modulus

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
theorem _root_.solution : ThinIff := by
  intro e q d _ _ X' θ
  obtain ⟨h1, h0⟩ := g_psi_at_modulus e q d
  constructor
  · intro h
    refine ⟨fun ψ hψ y hy => ?_, fun y hy => ?_⟩
    · rw [← h1 ψ hψ y]
      exact h ψ y hy
    · have := h 0 y hy
      rwa [h0 y, Complex.norm_real, Real.norm_eq_abs] at this
  · rintro ⟨hA, hB⟩ ψ y hy
    by_cases hψ : ψ = 0
    · subst hψ
      rw [h0 y, Complex.norm_real, Real.norm_eq_abs]
      exact hB y hy
    · rw [h1 ψ hψ y]
      exact hA ψ hψ y hy
end Formalism.LFunctionChainParameters.LBr2
