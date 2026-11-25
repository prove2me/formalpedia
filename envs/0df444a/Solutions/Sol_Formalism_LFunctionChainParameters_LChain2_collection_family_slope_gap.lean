-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LChain2.collection_family_slope_gap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:10:03.070043+00:00
-- url     : https://prove2.me/submissions/b5543c93-e475-4019-8f06-be495ad6e0d0

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
import Theorems.Thm_Formalism_LFunctionChainParameters_LChain2_modLat_cancel
import Theorems.Thm_Formalism_LFunctionChainParameters_LChain2_wmean_const
import Theorems.Thm_Formalism_LFunctionChainParameters_LChain2_coll_du
import Theorems.Thm_Formalism_RankGapBounds_WeightedMeanData_wmean_const


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
variable (v : InfinitePlace K) (m f T Mw : ℕ) (hb gG gE : ℝ)
namespace Formalism.LFunctionChainParameters.LChain2
theorem _root_.solution (hT : 4 ≤ T) (hMpos : 0 < Mw) :
    wmean (collFam K v m f T Mw (hbT K f T) gG gE).du
      (fun u => muDef ((collFam K v m f T Mw (hbT K f T) gG gE).b u) ((collFam K v m f T Mw (hbT K f T) gG gE).X u)
        ((collFam K v m f T Mw (hbT K f T) gG gE).N' u) - (collFam K v m f T Mw (hbT K f T) gG gE).h u)
      - muMinDef (collFam K v m f T Mw (hbT K f T) gG gE).b' (collFam K v m f T Mw (hbT K f T) gG gE).X'
          (collFam K v m f T Mw (hbT K f T) gG gE).cc ≤ 0 := by
  set F := collFam K v m f T Mw (hbT K f T) gG gE with hF
  have hN' : ∀ u, F.N' u = stdLat K (Fin ((T - 2) ^ f)) :=
    fun u => modLat_cancel K (tau0 K 2 0) (stdLat K (Fin ((T - 2) ^ f)))
  have hsum : ∑ u : Fin Mw, F.du u ≠ 0 := by
    have : 0 < ∑ u : Fin Mw, F.du u :=
      Finset.sum_pos (fun u _ => coll_du K v m f T Mw _ gG gE hT u) ⟨⟨0, hMpos⟩, Finset.mem_univ _⟩
    exact this.ne'
  have hfun : (fun u : Fin Mw => muDef (F.b u) (F.X u) (F.N' u) - F.h u) = fun _ =>
      muDef (Pi.basisFun K (Fin ((T - 2) ^ f)))
        (fun _ => ((Real.exp (-(dT f T) / 2) : ℝ) : ℂ) • 1) (stdLat K _) - F.h ⟨0, hMpos⟩ := by
    funext u
    exact congrArg (fun L => muDef (Pi.basisFun K (Fin ((T - 2) ^ f)))
        (fun _ => ((Real.exp (-(dT f T) / 2) : ℝ) : ℂ) • 1) L - F.h ⟨0, hMpos⟩) (hN' u)
  rw [hfun, wmean_const _ _ hsum]
  have hh : hbT K f T ≤ F.h ⟨0, hMpos⟩ := le_max_right _ _
  have hmin : muMinDef F.b' F.X' F.cc
      = muMinDef (Pi.basisFun K (Fin ((T - 2) ^ f))) (fun _ => 1) (stdLat K _) := rfl
  rw [hmin]
  unfold hbT at hh
  linarith
end Formalism.LFunctionChainParameters.LChain2
