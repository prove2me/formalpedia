-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.slopeLatticeData.muMaxDef_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:38:06.372621+00:00
-- url     : https://prove2.me/submissions/d103e827-6892-4a69-9478-41a76ca36c84

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
variable {K V ι : Type} [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
  [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι]
  [DecidableEq ι]
namespace Formalism.LFunctionChainParameters.slopeLatticeData
theorem _root_.solution (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    {L : Submodule (𝓞 K) V} (hL0 : L ≠ ⊥) {B : ℝ}
    (h : ∀ Q : Submodule (𝓞 K) V, Q ≤ L → Q ≠ ⊥ → muDef b X Q ≤ B) : muMaxDef b X L ≤ B := by
  have h1 : muMax (realize b X) L ≤
      (B + Real.log 2 - logDisc K / (Module.finrank ℚ K : ℝ)) / 2 := by
    unfold muMax
    refine csSup_le ⟨_, L, le_rfl, hL0, rfl⟩ ?_
    rintro t ⟨Q, hQL, hQ0, rfl⟩
    have := h Q hQL hQ0
    unfold muDef at this
    linarith
  unfold muMaxDef
  linarith
end Formalism.LFunctionChainParameters.slopeLatticeData
