-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LChain2.modLat_cancel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:37:53.216607+00:00
-- url     : https://prove2.me/submissions/10f6ffff-646f-4687-8de4-cadcf839a161

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
import Theorems.Thm_Formalism_LFunctionChainParameters_slopeLatticeData_idealPow_add
import Theorems.Thm_Formalism_LFunctionChainParameters_slopeLatticeData_idealPow_ne_zero
import Theorems.Thm_Formalism_LFunctionChainParameters_slopeLatticeData_idealSmul_inv_cancel


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
open Formalism.LFunctionChainParameters.ProjectiveLineModels (stdLat inclMat)
variable (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
namespace Formalism.LFunctionChainParameters.LChain2
theorem _root_.solution {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    (τ : slopeLatticeData.FinPl K →₀ ℤ) (L : Submodule (𝓞 K) V) :
    slopeLatticeData.modLat τ (Formalism.HermitianLatticesTheory.idealSmul
      ((slopeLatticeData.idealPow τ : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : Submodule (𝓞 K) K) L) = L := by
  have h1 : slopeLatticeData.idealPow (-τ) * slopeLatticeData.idealPow τ = (1 : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) := by
    rw [← slopeLatticeData.idealPow_add, neg_add_cancel]
    unfold slopeLatticeData.idealPow
    rw [Finsupp.prod_zero_index]
  unfold slopeLatticeData.modLat
  rw [eq_inv_of_mul_eq_one_left h1]
  exact slopeLatticeData.idealSmul_inv_cancel (slopeLatticeData.idealPow_ne_zero τ) L
end Formalism.LFunctionChainParameters.LChain2
