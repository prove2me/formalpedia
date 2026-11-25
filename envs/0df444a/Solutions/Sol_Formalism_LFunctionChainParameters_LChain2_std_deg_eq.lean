-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LChain2.std_deg_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:30:18.94718+00:00
-- url     : https://prove2.me/submissions/88be52d9-4e31-46d2-96c7-8898b3b654f3

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
open Formalism.LFunctionChainParameters.ProjectiveLineModels (stdLat)
variable {K : Type} [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
  {V ι : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι] [DecidableEq ι]
namespace Formalism.LFunctionChainParameters.LChain2
theorem _root_.solution (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (N : Submodule (𝓞 K) V)
    (h : rk (Formalism.HermitianLatticesTheory.realize b X) N ≠ 0) :
    deg (Formalism.HermitianLatticesTheory.realize b X) N = slope (Formalism.HermitianLatticesTheory.realize b X) N * (rk (Formalism.HermitianLatticesTheory.realize b X) N : ℝ) := by
  have h' : ((rk (Formalism.HermitianLatticesTheory.realize b X) N : ℕ) : ℝ) ≠ 0 := by exact_mod_cast h
  show deg (Formalism.HermitianLatticesTheory.realize b X) N
    = deg (Formalism.HermitianLatticesTheory.realize b X) N / (rk (Formalism.HermitianLatticesTheory.realize b X) N : ℝ) * (rk (Formalism.HermitianLatticesTheory.realize b X) N : ℝ)
  field_simp
end Formalism.LFunctionChainParameters.LChain2
