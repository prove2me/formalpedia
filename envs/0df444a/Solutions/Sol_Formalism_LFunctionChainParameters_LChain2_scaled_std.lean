-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LChain2.scaled_std
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:12:41.114849+00:00
-- url     : https://prove2.me/submissions/23076c35-697f-48ba-ac3f-24a591c491d9

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
import Theorems.Thm_Formalism_LFunctionChainParameters_LChain2_mu_std
import Theorems.Thm_Formalism_LFunctionChainParameters_LChain2_twistP
import Theorems.Thm_Formalism_LFunctionChainParameters_ProjectiveLineModels_standard_lattice_fg
import Theorems.Thm_Formalism_LFunctionChainParameters_ProjectiveLineModels_standard_lattice_ne_bot


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
theorem _root_.solution (n : Type) [Fintype n] [DecidableEq n] [Nonempty n] (c : ℝ) (hc : 0 < c) :
    muDef (Pi.basisFun K n) (fun _ => (c : ℂ) • (1 : Matrix n n ℂ)) (stdLat K n) = 2 * Real.log c ∧
    muMaxDef (Pi.basisFun K n) (fun _ => (c : ℂ) • (1 : Matrix n n ℂ)) (stdLat K n)
      = muMaxDef (Pi.basisFun K n) (fun _ => 1) (stdLat K n) + 2 * Real.log c := by
  have hX : ∀ v : InfinitePlace K, IsUnit ((1 : Matrix n n ℂ)).det := by simp
  have h := (twistP K (n → K) n (Pi.basisFun K n) (fun _ => 1) (fun _ => c) hX (fun _ => hc) (stdLat K n)
    (ProjectiveLineModels.standard_lattice_fg K n)).2.2.1 (ProjectiveLineModels.standard_lattice_ne_bot K n)
  have ht : (1 / (nPl K : ℝ)) * ∑ _v : InfinitePlace K, Real.log c = Real.log c := by
    have hn : (nPl K : ℝ) ≠ 0 := by
      have : 0 < nPl K := Fintype.card_pos
      exact_mod_cast this.ne'
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    unfold nPl at hn ⊢
    field_simp
  simp only [ht] at h
  exact ⟨by rw [h.1, mu_std]; ring, h.2.1⟩
end Formalism.LFunctionChainParameters.LChain2
