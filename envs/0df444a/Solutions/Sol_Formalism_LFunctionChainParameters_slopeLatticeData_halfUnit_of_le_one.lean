-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.slopeLatticeData.halfUnit_of_le_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:58:07.358792+00:00
-- url     : https://prove2.me/submissions/96e46ff2-2c2f-4197-9364-991d2e824df1

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
theorem _root_.solution (w : Ideal (𝓞 K)) [hw : w.IsPrime] {J : FI} (h : J ≤ 1) :
    HalfUnit w J := by
  refine ⟨1, fun h1 => hw.ne_top ((Ideal.eq_top_iff_one w).2 h1), fun x hx => ?_⟩
  obtain ⟨y, hy⟩ := (FractionalIdeal.mem_one_iff _).1 (h hx)
  exact ⟨y, by rw [hy, map_one, one_mul]⟩
end Formalism.LFunctionChainParameters.slopeLatticeData
