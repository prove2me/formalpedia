-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LBrDiv.ne_bot_of_span
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:34:59.630853+00:00
-- url     : https://prove2.me/submissions/1ff629a6-d507-4bda-8b92-39cec6e0b3eb

import Definitions.Def_Formalism_SizeWindowBrackets_SBrDiv
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_LevelOfCongruence
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_StronglyIrreducible
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DualPl
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SizeMu
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_Rerealize
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_PBrDiv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open Formalism.HN
noncomputable section
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.LBrDiv
open Formalism Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.LErr Formalism.LFunctionChainParameters.LChain2
namespace Formalism.LFunctionChainParameters.LBrDiv
theorem _root_.solution {K V ι : Type} [Field K] [NumberField K] [AddCommGroup V]
    [Module K V] [Module (𝓞 K) V] [Nonempty ι]
    (b : Basis ι K V) (A : Submodule (𝓞 K) V) (hsp : Submodule.span K (A : Set V) = ⊤) : A ≠ ⊥ := by
  rintro rfl
  have h0 : Submodule.span K (((⊥ : Submodule (𝓞 K) V) : Set V)) = ⊥ := by simp
  rw [h0] at hsp
  obtain ⟨i⟩ := (inferInstance : Nonempty ι)
  have : b i ∈ (⊥ : Submodule K V) := by rw [hsp]; trivial
  exact b.ne_zero i (by simpa using this)
end Formalism.LFunctionChainParameters.LBrDiv
