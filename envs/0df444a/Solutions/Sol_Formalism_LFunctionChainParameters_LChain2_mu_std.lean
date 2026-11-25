-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LChain2.mu_std
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:43:37.709143+00:00
-- url     : https://prove2.me/submissions/6b028c93-09c6-440c-9032-99e4c14ce2da

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
import Theorems.Thm_Formalism_LFunctionChainParameters_LChain2_gram_std
import Theorems.Thm_Formalism_HN_height_gram_determinant
import Theorems.Thm_Formalism_LFunctionChainParameters_ProjectiveLineModels_standard_lattice_fg
import Theorems.Thm_Formalism_LFunctionChainParameters_ProjectiveLineModels_standard_lattice_ne_bot
import Theorems.Thm_Formalism_LFunctionChainParameters_slopeLatticeData_muDef_eq_log


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
theorem _root_.solution (n : Type) [Fintype n] [DecidableEq n] [Nonempty n] :
    muDef (Pi.basisFun K n) (fun _ => 1) (stdLat K n) = 0 := by
  have hX : ∀ v : InfinitePlace K, IsUnit ((1 : Matrix n n ℂ)).det := by simp
  have hr : Set.range (fun a : Fin (Fintype.card n) => Pi.basisFun K n ((Fintype.equivFin n).symm a))
      = Set.range (Pi.basisFun K n) := EquivLike.range_comp _ (Fintype.equivFin n).symm
  have h := (height_gram_determinant K (n → K) n (Pi.basisFun K n) (fun _ => 1) hX (Fintype.card n)
    (fun a => Pi.basisFun K n ((Fintype.equivFin n).symm a))
    ((Pi.basisFun K n).linearIndependent.comp _ (Fintype.equivFin n).symm.injective)).1
  rw [hr] at h
  rw [slopeLatticeData.muDef_eq_log _ _ hX (ProjectiveLineModels.standard_lattice_fg K n) (ProjectiveLineModels.standard_lattice_ne_bot K n)]
  have h1 : ht (Pi.basisFun K n) (fun _ => 1) (stdLat K n) = 1 := by
    unfold stdLat
    rw [h]
    simp only [gram_std, Matrix.det_one, Complex.one_re, Finset.prod_const_one]
  rw [h1]
  simp
end Formalism.LFunctionChainParameters.LChain2
