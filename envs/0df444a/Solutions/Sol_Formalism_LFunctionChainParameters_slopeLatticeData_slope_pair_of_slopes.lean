-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.slopeLatticeData.slope_pair_of_slopes
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:15:27.988897+00:00
-- url     : https://prove2.me/submissions/6b1baafd-2340-4990-8410-7f4bfecf57c5

import Definitions.Def_Formalism_SizeWindowBrackets_SlopesHypothesisFinitePlaces
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SizeMu
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_HtGram
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_MuChar
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DualPl
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_WeightedMeanLemmaNeedsDegree
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_ExistsNsmulMem
import Theorems.Thm_Formalism_LFunctionChainParameters_slopeLatticeData_slope_via_lengths

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
namespace Formalism.LFunctionChainParameters.slopeLatticeData
theorem _root_.solution : SlopesHypothesisFinitePlaces := by
  intro K _ _ _ _ J V ι _ _ _ _ _ _ b X hX σ τ M N β Sg0 dr hM hM0 hN hrk hβ hSg
  constructor
  · intro u
    have := (slope_via_lengths K (V u) (ι u) (b u) (X u) (hX u) (σ u) (τ u) (M u) (N u) (β u) (hM u)
      (hM0 u) (hN u) (hrk u) (hβ u)).2.2.1
    rw [hSg u] at this
    exact this
  · intro u
    have := (slope_via_lengths K (V u) (ι u) (b u) (X u) (hX u) (σ u) (τ u) (M u) (N u) (β u) (hM u)
      (hM0 u) (hN u) (hrk u) (hβ u)).2.2.2
    rw [hSg u] at this
    exact this
end Formalism.LFunctionChainParameters.slopeLatticeData
