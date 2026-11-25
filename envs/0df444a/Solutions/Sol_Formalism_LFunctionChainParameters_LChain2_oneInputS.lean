-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LChain2.oneInputS
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:01:05.717355+00:00
-- url     : https://prove2.me/submissions/32495f32-0dcd-4a9d-be59-b68810c5ba88

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
import Theorems.Thm_Formalism_LFunctionChainParameters_ProjectiveLineModels_hs_sq_one


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
theorem _root_.solution (I n : Type) [Fintype n] [DecidableEq n] :
    MatrixLatticeEstimates.InputSG (I := I) (ι := fun _ => n) (fun _ => (1 : Matrix n n ℂ)) (fun _ => 1)
      (Fintype.card n : ℝ) 0 0 0 := by
  have hK : ∀ i j : I, MatrixLatticeEstimates.KpG (I := I) (ι := fun _ => n) (fun _ => (1 : Matrix n n ℂ)) (fun _ => 1) i j = 1 := by
    intro i j
    simp [MatrixLatticeEstimates.KpG]
  refine ⟨fun i j _ => ?_, fun i => ?_, ?_⟩
  · rw [hK, ProjectiveLineModels.hs_sq_one]
    rcases Nat.eq_zero_or_pos (Fintype.card n) with h | h
    · simp [h]
    · have : (0 : ℝ) < (Fintype.card n : ℝ) := by exact_mod_cast h
      field_simp
      simp
  · unfold MatrixLatticeEstimates.KdG
    rw [hK]
    simp [HilbertSchmidtNormSquare.hsSq]
  · simp
end Formalism.LFunctionChainParameters.LChain2
