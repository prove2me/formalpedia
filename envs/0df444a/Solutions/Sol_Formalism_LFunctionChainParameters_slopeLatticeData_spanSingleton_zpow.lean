-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.slopeLatticeData.spanSingleton_zpow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:31:59.013426+00:00
-- url     : https://prove2.me/submissions/b0c927a0-2304-48f2-9eeb-d5469f4ba379

import Definitions.Def_Formalism_SizeWindowBrackets_SlopesHypothesisFinitePlaces
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SizeMu
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_HtGram
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_MuChar
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DualPl
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_WeightedMeanLemmaNeedsDegree
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_ExistsNsmulMem

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
theorem _root_.solution (x : K) (k : ℤ) :
    (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) x : FI) ^ k =
      FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) (x ^ k) := by
  obtain ⟨n, rfl | rfl⟩ := k.eq_nat_or_neg
  · rw [zpow_natCast, zpow_natCast, FractionalIdeal.spanSingleton_pow]
  · rw [zpow_neg, zpow_neg, zpow_natCast, zpow_natCast, FractionalIdeal.spanSingleton_pow,
      FractionalIdeal.spanSingleton_inv]
end Formalism.LFunctionChainParameters.slopeLatticeData
