-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.slopeLatticeData.fg_of_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:07:01.921592+00:00
-- url     : https://prove2.me/submissions/8cfa2954-6850-48f7-89a0-f968761852bb

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
variable {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
namespace Formalism.LFunctionChainParameters.slopeLatticeData
theorem _root_.solution {N M : Submodule (𝓞 K) V} (hM : M.FG) (h : N ≤ M) : N.FG := by
  have : Module.Finite (𝓞 K) M := Module.Finite.iff_fg.mpr hM
  exact Submodule.FG.of_le_of_isNoetherian h
end Formalism.LFunctionChainParameters.slopeLatticeData
