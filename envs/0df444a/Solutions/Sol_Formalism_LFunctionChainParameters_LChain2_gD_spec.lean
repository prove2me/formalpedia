-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LChain2.gD_spec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T02:27:33.670129+00:00
-- url     : https://prove2.me/submissions/7f1deecb-6216-4023-98cb-75385dd31113

import Definitions.Def_Formalism_SizeWindowBrackets_Chain2aCoreNoAnalytic
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_PChain
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_SlopeInequalityOfLattices
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_GaloisMapComplexConjugation
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_AdmissibleSchurLemma
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_OneLeThresholdMulPowers
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_StronglyIrreducible
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_ProjectiveLines
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SlopeIneqMean
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_HtGram
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_PolygonSlopeSum
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SizeMu
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_ChainLatticeSizesModelEventually

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField Matrix
open Formalism.HN
noncomputable section
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.LChain2
open Formalism Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LErr Formalism.LFunctionChainParameters.LChain
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H] {Ω : Type} {W : Ω → H → Type} {m : ℕ}
namespace Formalism.LFunctionChainParameters.LChain2
theorem _root_.solution (D : ArithData H) (hD : HostFacts D) (i : ℕ) :
    gD D i - i • D.frob D.d ∈ D.inertia D.d ∧ ¬ InPhi (gD D i) := by
  unfold gD
  split_ifs with h
  · refine ⟨(hD.inertia_d _).2 (Or.inr (by abel)), ?_⟩
    unfold InPhi at h ⊢
    show (i • D.frob D.d).1.1 + 1 ≠ 0
    rw [h]
    decide
  · exact ⟨(hD.inertia_d _).2 (Or.inl (by abel)), h⟩
end Formalism.LFunctionChainParameters.LChain2
