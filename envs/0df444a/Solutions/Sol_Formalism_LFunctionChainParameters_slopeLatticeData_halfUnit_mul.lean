-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.slopeLatticeData.halfUnit_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:30:47.828887+00:00
-- url     : https://prove2.me/submissions/6301ba1f-6a9e-44a9-81d7-dbdf15ab891c

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
theorem _root_.solution (w : Ideal (𝓞 K)) [hw : w.IsPrime] {I J : FI} (hI : HalfUnit w I)
    (hJ : HalfUnit w J) : HalfUnit w (I * J) := by
  obtain ⟨t1, ht1, h1⟩ := hI
  obtain ⟨t2, ht2, h2⟩ := hJ
  refine ⟨t1 * t2, fun h => (hw.mem_or_mem h).elim ht1 ht2, fun x hx => ?_⟩
  refine FractionalIdeal.mul_induction_on hx ?_ ?_
  · intro i hi j hj
    obtain ⟨y1, hy1⟩ := h1 i hi
    obtain ⟨y2, hy2⟩ := h2 j hj
    exact ⟨y1 * y2, by rw [map_mul, map_mul, hy1, hy2]; ring⟩
  · rintro x y ⟨a, ha⟩ ⟨c, hc⟩
    exact ⟨a + c, by rw [map_add, ha, hc]; ring⟩
end Formalism.LFunctionChainParameters.slopeLatticeData
