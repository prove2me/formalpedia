-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.slopeLatticeData.local_ideal_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:44:09.406306+00:00
-- url     : https://prove2.me/submissions/bc19b09a-0b5a-4490-bc67-7eb230529407

import Definitions.Def_Formalism_SizeWindowBrackets_SlopesHypothesisFinitePlaces
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SizeMu
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_HtGram
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_MuChar
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DualPl
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_WeightedMeanLemmaNeedsDegree
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_ExistsNsmulMem
import Theorems.Thm_Formalism_LFunctionChainParameters_slopeLatticeData_idealSmul_mul
import Theorems.Thm_Formalism_LFunctionChainParameters_slopeLatticeData_idealSmul_spanSingleton
import Theorems.Thm_Formalism_LFunctionChainParameters_slopeLatticeData_wUnit_idealPow
import Theorems.Thm_Formalism_LFunctionChainParameters_slopeLatticeData_spanSingleton_zpow
import Theorems.Thm_Formalism_LFunctionChainParameters_slopeLatticeData_span_loc_idealSmul

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
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
namespace Formalism.LFunctionChainParameters.slopeLatticeData
theorem _root_.solution : LocIdealPow := by
  intro K V _ _ _ _ _ _ w _ _ ϖ h1 h2 n M
  have := w.2.isPrime
  have hϖ0 : ϖ ≠ 0 := by
    rintro rfl; exact h2 (Ideal.zero_mem _)
  have hϖK : algebraMap (𝓞 K) K ϖ ≠ 0 := by
    intro h0
    exact hϖ0 (FaithfulSMul.algebraMap_injective (𝓞 K) K (by simpa using h0))
  have hU := wUnit_idealPow w h1 h2 n
  have hPw0 : (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) (algebraMap (𝓞 K) K ϖ) :
      FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ^ (n w) ≠ 0 :=
    zpow_ne_zero _ (FractionalIdeal.spanSingleton_ne_zero_iff.2 hϖK)
  have hfac : idealPow n = idealPow n *
      ((FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) (algebraMap (𝓞 K) K ϖ) :
        FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ^ (n w))⁻¹ *
      FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) (algebraMap (𝓞 K) K ϖ ^ n w) := by
    rw [← spanSingleton_zpow, mul_assoc, inv_mul_cancel₀ hPw0, mul_one]
  conv_lhs => rw [hfac, FractionalIdeal.coe_mul, idealSmul_mul, idealSmul_spanSingleton]
  rw [span_loc_idealSmul w.1 hU, Submodule.map_coe]
  rfl
end Formalism.LFunctionChainParameters.slopeLatticeData
