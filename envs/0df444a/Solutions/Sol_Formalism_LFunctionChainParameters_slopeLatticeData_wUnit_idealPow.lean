-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.slopeLatticeData.wUnit_idealPow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:35:07.087335+00:00
-- url     : https://prove2.me/submissions/10ab0d8e-f779-4238-b95c-2db2bd562880

import Definitions.Def_Formalism_SizeWindowBrackets_SlopesHypothesisFinitePlaces
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SizeMu
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_HtGram
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_MuChar
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DualPl
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_WeightedMeanLemmaNeedsDegree
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_ExistsNsmulMem
import Theorems.Thm_Formalism_LFunctionChainParameters_slopeLatticeData_wUnit_one
import Theorems.Thm_Formalism_LFunctionChainParameters_slopeLatticeData_wUnit_mul
import Theorems.Thm_Formalism_LFunctionChainParameters_slopeLatticeData_wUnit_zpow
import Theorems.Thm_Formalism_LFunctionChainParameters_slopeLatticeData_wUnit_other
import Theorems.Thm_Formalism_LFunctionChainParameters_slopeLatticeData_wUnit_self
import Theorems.Thm_Formalism_LFunctionChainParameters_slopeLatticeData_idealPow_add

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
noncomputable section
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.slopeLatticeData
open Formalism.HN Formalism.HermitianLatticesTheory
variable {K : Type} [Field K] [NumberField K]
local notation "FI" => FractionalIdeal (nonZeroDivisors (𝓞 K)) K
namespace Formalism.LFunctionChainParameters.slopeLatticeData
theorem _root_.solution (w : FinPl K) {ϖ : 𝓞 K} (h1 : ϖ ∈ w.1) (h2 : ϖ ∉ w.1 ^ 2)
    (n : FinPl K →₀ ℤ) : WUnit w.1 (idealPow n *
      ((FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) (algebraMap (𝓞 K) K ϖ) : FI) ^
        (n w))⁻¹) := by
  classical
  have := w.2.isPrime
  have hϖ0 : ϖ ≠ 0 := by
    rintro rfl; exact h2 (Ideal.zero_mem _)
  have hϖK : algebraMap (𝓞 K) K ϖ ≠ 0 := by
    intro h0
    exact hϖ0 (FaithfulSMul.algebraMap_injective (𝓞 K) K (by simpa using h0))
  set Pw : FI := FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) (algebraMap (𝓞 K) K ϖ)
    with hPw
  have hPw0 : Pw ≠ 0 := FractionalIdeal.spanSingleton_ne_zero_iff.2 hϖK
  induction n using Finsupp.induction_linear with
  | zero =>
    have : idealPow (0 : FinPl K →₀ ℤ) = 1 := by unfold idealPow; exact Finsupp.prod_zero_index
    rw [this, Finsupp.zero_apply, zpow_zero, inv_one, mul_one]
    exact wUnit_one w.1
  | add f g hf hg =>
    rw [idealPow_add, Finsupp.add_apply, zpow_add₀ hPw0, mul_inv, mul_mul_mul_comm]
    exact wUnit_mul w.1 hf hg
  | single a k =>
    have : idealPow (Finsupp.single a k) = (a.1 : FI) ^ k := by
      unfold idealPow
      exact Finsupp.prod_single_index (zpow_zero _)
    rw [this, Finsupp.single_apply]
    by_cases ha : a = w
    · subst ha
      rw [if_pos rfl, ← inv_zpow, ← mul_zpow]
      exact wUnit_zpow a.1 (wUnit_self a h1 h2) k
    · rw [if_neg ha, zpow_zero, inv_one, mul_one]
      exact wUnit_zpow w.1 (wUnit_other w a ha) k
end Formalism.LFunctionChainParameters.slopeLatticeData
