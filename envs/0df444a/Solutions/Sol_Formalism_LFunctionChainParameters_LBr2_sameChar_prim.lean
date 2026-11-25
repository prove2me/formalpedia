-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LBr2.sameChar_prim
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T02:26:57.840391+00:00
-- url     : https://prove2.me/submissions/dd404af0-7a69-4ee1-b4bf-66f3612512b0

import Definitions.Def_Formalism_SizeWindowBrackets_SmoothedRemainderRealIntegralFormula
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_GaloisMapComplexConjugation
import Definitions.Def_Formalism_LandauZeroFreeBounds_SiegelWalfiszAPOfSiegelLower
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_PrimeCongruenceConditions
import Theorems.Thm_Formalism_FrobeniusOrbits_Group_key


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
theorem _root_.solution {N M : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hM : M ∣ N) (χ' : DirichletCharacter ℂ M)
    (hp : χ'.IsPrimitive) (hχ : χ = changeLevel hM χ') : SameChar χ.primitiveCharacter χ' := by
  have hc : χ.conductor = M := by
    rw [hχ, conductor_changeLevel]
    exact hp
  have key : ∀ (c : ℕ) (χ₀ : DirichletCharacter ℂ c) (hcN : c ∣ N), changeLevel hcN χ₀ = χ → c = M →
      SameChar χ₀ χ' := by
    intro c χ₀ hcN h1 h2
    subst h2
    have h3 : χ₀ = χ' := changeLevel_injective hcN (h1.trans hχ)
    subst h3
    exact ⟨rfl, fun _ => rfl⟩
  exact key _ _ (conductor_dvd_level χ) (changeLevel_primitiveCharacter χ) hc
end Formalism.LFunctionChainParameters.LBr2
