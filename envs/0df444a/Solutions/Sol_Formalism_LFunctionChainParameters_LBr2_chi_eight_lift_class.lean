-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LBr2.chi_eight_lift_class
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T02:48:14.190395+00:00
-- url     : https://prove2.me/submissions/1d826129-cdc6-49bb-87ad-8097f887b6ae

import Definitions.Def_Formalism_SizeWindowBrackets_SmoothedRemainderRealIntegralFormula
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_GaloisMapComplexConjugation
import Definitions.Def_Formalism_LandauZeroFreeBounds_SiegelWalfiszAPOfSiegelLower
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_PrimeCongruenceConditions
import Theorems.Thm_Formalism_LFunctionChainParameters_LBr2_chi_eight_lift_values

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
theorem _root_.solution (e : ℕ) (h8 : 8 ∣ 2 ^ (e + 2)) (v : (ZMod (2 ^ (e + 2)))ˣ) (k : ℕ)
    (hk : FrobeniusOrbits.hcl e v = (FrobeniusOrbits.hcl e (TwoAdicCyclotomicDecomposition.u5 (e + 2))) ^ k) :
    changeLevel h8 chi8 (v : ZMod (2 ^ (e + 2))) = (-1) ^ k := by
  obtain ⟨hm, h5⟩ := chi_eight_lift_values e h8
  set F := (changeLevel h8 chi8).toUnitHom with hF
  have hFm : F (-1) = 1 := by
    apply Units.ext
    rw [hF, MulChar.coe_toUnitHom, hm]
    rfl
  have hF5 : ((F (TwoAdicCyclotomicDecomposition.u5 (e + 2)) : ℂˣ) : ℂ) = -1 := by
    rw [hF, MulChar.coe_toUnitHom, h5]
  have hmem : v⁻¹ * (TwoAdicCyclotomicDecomposition.u5 (e + 2)) ^ k ∈ Subgroup.zpowers (-1 : (ZMod (2 ^ (e + 2)))ˣ) := by
    apply QuotientGroup.eq.1
    exact hk
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 hmem
  have h1 : F (v⁻¹ * (TwoAdicCyclotomicDecomposition.u5 (e + 2)) ^ k) = 1 := by
    rw [← hj, map_zpow, hFm, one_zpow]
  rw [map_mul, map_inv, map_pow, inv_mul_eq_one] at h1
  rw [← MulChar.coe_toUnitHom, ← hF, h1, Units.val_pow_eq_pow_val, hF5]
end Formalism.LFunctionChainParameters.LBr2
