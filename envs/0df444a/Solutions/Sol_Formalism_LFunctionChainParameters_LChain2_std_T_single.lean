-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LChain2.std_T_single
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T02:29:52.177615+00:00
-- url     : https://prove2.me/submissions/3b113010-10f7-4c3d-b578-0a55b180fd1f

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
import Theorems.Thm_Formalism_LFunctionChainParameters_LChain2_std_T_fg
import Theorems.Thm_Formalism_LFunctionChainParameters_LChain2_std_T_ne
import Theorems.Thm_Formalism_HN_height_gram_determinant
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
open Formalism.LFunctionChainParameters.ProjectiveLineModels (stdLat)
variable (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
  (n : Type) [Fintype n] [DecidableEq n]
variable {K n}
namespace Formalism.LFunctionChainParameters.LChain2
theorem _root_.solution (a : n) :
    rkK (standardSpanAlt K n {a}) = 1 ∧ muDef (Pi.basisFun K n) (fun _ => 1) (standardSpanAlt K n {a}) = 0 := by
  have hX : ∀ v : InfinitePlace K, IsUnit ((1 : Matrix n n ℂ)).det := by simp
  have hr : Set.range (fun _ : Fin 1 => Pi.basisFun K n a) = (Pi.basisFun K n) '' ((({a} : Finset n)) : Set n) := by
    simp
  have hli : LinearIndependent K (fun _ : Fin 1 => Pi.basisFun K n a) :=
    LinearIndependent.of_subsingleton 0 ((Pi.basisFun K n).ne_zero a)
  have h := (height_gram_determinant K (n → K) n (Pi.basisFun K n) (fun _ => 1) hX 1
    (fun _ => Pi.basisFun K n a) hli).1
  rw [hr] at h
  have hg : ∀ v : InfinitePlace K, gramPl (Pi.basisFun K n) (fun _ => 1) v (fun _ : Fin 1 => Pi.basisFun K n a) = 1 := by
    intro v
    ext i j
    simp [gramPl, Formalism.HermitianLatticesTheory.majAt, Formalism.HermitianLatticesTheory.fcoord, Formalism.HermitianLatticesTheory.vecAt, Matrix.one_apply, Pi.single_apply,
      Subsingleton.elim i j]
  have hrk : rkK (standardSpanAlt K n {a}) = 1 := by
    unfold rkK standardSpanAlt
    rw [Submodule.span_span_of_tower, Finset.coe_singleton, Set.image_singleton]
    exact finrank_span_singleton ((Pi.basisFun K n).ne_zero a)
  refine ⟨hrk, ?_⟩
  rw [slopeLatticeData.muDef_eq_log _ _ hX (std_T_fg {a}) (std_T_ne (Finset.singleton_nonempty a))]
  have h1 : ht (Pi.basisFun K n) (fun _ => 1) (standardSpanAlt K n {a}) = 1 := by
    unfold standardSpanAlt
    rw [h]
    simp only [hg, Matrix.det_one, Complex.one_re, Finset.prod_const_one]
  rw [h1]
  simp
end Formalism.LFunctionChainParameters.LChain2
