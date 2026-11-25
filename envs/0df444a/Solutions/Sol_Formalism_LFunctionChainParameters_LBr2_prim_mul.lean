-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LBr2.prim_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:45:20.733206+00:00
-- url     : https://prove2.me/submissions/93f919dd-23f6-4510-9b38-2cbc6e67deb2

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
theorem _root_.solution {N m n : ℕ} [NeZero N] (hm : m ∣ N) (hn : n ∣ N) (hco : m.Coprime n) (hN : N = m * n)
    (χ₁ : DirichletCharacter ℂ m) (χ₂ : DirichletCharacter ℂ n) (h1 : χ₁.IsPrimitive) (h2 : χ₂.IsPrimitive) :
    (changeLevel hm χ₁ * changeLevel hn χ₂).IsPrimitive := by
  have cA : (changeLevel hm χ₁).conductor = m := by rw [conductor_changeLevel]; exact h1
  have cB : (changeLevel hn χ₂).conductor = n := by rw [conductor_changeLevel]; exact h2
  generalize changeLevel hm χ₁ = A at *
  generalize changeLevel hn χ₂ = B at *
  have d1 : m ∣ (A * B).conductor.lcm n := by
    have h := conductor_mul_dvd_lcm_conductor (A * B) B⁻¹
    rwa [mul_inv_cancel_right, conductor_inv, cA, cB] at h
  have d2 : n ∣ (A * B).conductor.lcm m := by
    have h := conductor_mul_dvd_lcm_conductor (B * A) A⁻¹
    rwa [mul_inv_cancel_right, conductor_inv, cA, cB, mul_comm B A] at h
  have e1 : m ∣ (A * B).conductor :=
    hco.dvd_of_dvd_mul_right (d1.trans (Nat.lcm_dvd_mul _ _))
  have e2 : n ∣ (A * B).conductor :=
    hco.symm.dvd_of_dvd_mul_right (d2.trans (Nat.lcm_dvd_mul _ _))
  rw [isPrimitive_def]
  have e3 : N ∣ (A * B).conductor := by
    have h := hco.mul_dvd_of_dvd_of_dvd e1 e2
    rwa [← hN] at h
  exact Nat.dvd_antisymm (conductor_dvd_level _) e3
end Formalism.LFunctionChainParameters.LBr2
