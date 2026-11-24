-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.slopeLatticeData.ht_ideal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:30:48.775843+00:00
-- url     : https://prove2.me/submissions/07284371-0527-40d4-bf46-565e3c5ea5b5

import Definitions.Def_Formalism_SizeWindowBrackets_SlopesHypothesisFinitePlaces
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SizeMu
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_HtGram
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_MuChar
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DualPl
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_WeightedMeanLemmaNeedsDegree
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_ExistsNsmulMem
import Theorems.Thm_Formalism_LFunctionChainParameters_slopeLatticeData_ht_index
import Theorems.Thm_Formalism_HN_DualPolygon_twist_index
import Theorems.Thm_Formalism_HN_DualPolygon_twist_span_smul


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
    (hX : ∀ v, IsUnit (X v).det) {L : Submodule (𝓞 K) V} (hL : L.FG) {J : Ideal (𝓞 K)}
    (hJ : J ≠ ⊥) : ht b X (J • L) = ht b X L * (Ideal.absNorm J : ℝ) ^ rkK L := by
  have hfd : FiniteDimensional K V := Module.Finite.of_basis b
  have hrk : rkK (J • L) = rkK L := by
    unfold rkK; rw [Formalism.HN.DualPolygon.twist_span_smul L J hJ]
  rw [ht_index b X hX hL Submodule.smul_le_right hrk, Formalism.HN.DualPolygon.twist_index L hL J hJ]
  push_cast
  rfl
end Formalism.LFunctionChainParameters.slopeLatticeData
