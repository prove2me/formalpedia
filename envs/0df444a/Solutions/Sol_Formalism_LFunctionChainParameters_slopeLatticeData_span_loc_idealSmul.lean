-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.slopeLatticeData.span_loc_idealSmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:46:49.50029+00:00
-- url     : https://prove2.me/submissions/01522244-3da9-4890-bb92-8268d32641ea

import Definitions.Def_Formalism_SizeWindowBrackets_SlopesHypothesisFinitePlaces
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SizeMu
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_HtGram
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_MuChar
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DualPl
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_WeightedMeanLemmaNeedsDegree
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_ExistsNsmulMem
import Theorems.Thm_Formalism_LFunctionChainParameters_slopeLatticeData_idealSmul_inv_cancel
import Theorems.Thm_Formalism_LFunctionChainParameters_slopeLatticeData_idealSmul_le_span_loc

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
theorem _root_.solution (w : Ideal (𝓞 K)) [w.IsPrime] [Module (Localization.AtPrime w) V]
    [IsScalarTower (𝓞 K) (Localization.AtPrime w) V] {J : FI} (hJ : WUnit w J)
    (L : Submodule (𝓞 K) V) :
    Submodule.span (Localization.AtPrime w)
      ((idealSmul (J : Submodule (𝓞 K) K) L : Submodule (𝓞 K) V) : Set V) =
      Submodule.span (Localization.AtPrime w) (L : Set V) := by
  apply le_antisymm
  · exact Submodule.span_le.2 fun x hx => idealSmul_le_span_loc w hJ.2.1 L hx
  · refine Submodule.span_le.2 fun x hx => ?_
    have h := idealSmul_le_span_loc w hJ.2.2 (idealSmul (J : Submodule (𝓞 K) K) L)
    rw [idealSmul_inv_cancel hJ.1] at h
    exact h hx
end Formalism.LFunctionChainParameters.slopeLatticeData
