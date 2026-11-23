-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.slopeLatticeData.idealSmul_fg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:57:10.731026+00:00
-- url     : https://prove2.me/submissions/dd697412-27f8-4fcc-bef5-160a2e3446b5

import Definitions.Def_Formalism_SizeWindowBrackets_SlopesHypothesisFinitePlaces
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SizeMu
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_HtGram
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_MuChar
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DualPl
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_WeightedMeanLemmaNeedsDegree
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_ExistsNsmulMem
import Theorems.Thm_Formalism_LFunctionChainParameters_slopeLatticeData_idealSmul_mul
import Theorems.Thm_Formalism_LFunctionChainParameters_slopeLatticeData_idealSmul_coeIdeal
import Theorems.Thm_Formalism_LFunctionChainParameters_slopeLatticeData_idealSmul_spanSingleton

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
theorem _root_.solution (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) {L : Submodule (𝓞 K) V}
    (hL : L.FG) : (idealSmul (I : Submodule (𝓞 K) K) L).FG := by
  obtain ⟨a, J, -, hI⟩ := FractionalIdeal.exists_eq_spanSingleton_mul I
  rw [hI, FractionalIdeal.coe_mul, idealSmul_mul, idealSmul_coeIdeal, idealSmul_spanSingleton]
  exact (Submodule.FG.smul (IsNoetherian.noetherian J) hL).map _
end Formalism.LFunctionChainParameters.slopeLatticeData
