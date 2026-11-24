-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.slopeLatticeData.span_idealSmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:46:56.660885+00:00
-- url     : https://prove2.me/submissions/3ed041ce-aa31-4a79-a81c-6f9c7a51283f

import Definitions.Def_Formalism_SizeWindowBrackets_SlopesHypothesisFinitePlaces
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SizeMu
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_HtGram
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_MuChar
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DualPl
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_WeightedMeanLemmaNeedsDegree
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_ExistsNsmulMem
import Theorems.Thm_Formalism_LFunctionChainParameters_slopeLatticeData_idealSmul_le_span
import Theorems.Thm_Formalism_LFunctionChainParameters_slopeLatticeData_idealSmul_inv_cancel

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
theorem _root_.solution {I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K} (hI : I ≠ 0)
    (L : Submodule (𝓞 K) V) :
    Submodule.span K ((idealSmul (I : Submodule (𝓞 K) K) L : Submodule (𝓞 K) V) : Set V) =
      Submodule.span K (L : Set V) := by
  apply le_antisymm
  · exact Submodule.span_le.2 (fun x hx => idealSmul_le_span _ _ hx)
  · refine Submodule.span_le.2 (fun x hx => ?_)
    have h := idealSmul_le_span ((I⁻¹ : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) :
      Submodule (𝓞 K) K) (idealSmul (I : Submodule (𝓞 K) K) L)
    rw [idealSmul_inv_cancel hI] at h
    exact h hx
end Formalism.LFunctionChainParameters.slopeLatticeData
