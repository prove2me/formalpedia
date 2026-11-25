-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LChain2.coll_place
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:28:42.414895+00:00
-- url     : https://prove2.me/submissions/3cbe8faf-1495-4f7a-a2c8-c0c413cffd62

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
import Theorems.Thm_Formalism_LFunctionChainParameters_LChain2_lenSelf0
import Theorems.Thm_Formalism_LFunctionChainParameters_LChain2_model_place
import Theorems.Thm_Formalism_LFunctionChainParameters_LChain2_twist_vector_at_zero
import Theorems.Thm_Formalism_LFunctionChainParameters_LChain2_bump_cancel

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
theorem _root_.solution (bb : ℝ) (hm : 1 ≤ m) (hf : 1 ≤ f) (hTp : T.Prime) (hne : 2 ≠ T)
    (hT4 : 4 * f ≤ T) (hsmall : 4 * (f : ℝ) / (T : ℝ) * bb ^ 2 + dT f T ≤ 1) :
    (collFam K v m f T Mw hb gG gE).PlaceHyp f bb := by
  have hP := model_place K v m f T 2 0 Mw hb bb hm hf hTp Nat.prime_two hne hT4 hsmall
    (by push_cast; nlinarith [sq_nonneg bb])
  obtain ⟨a1, a2, -, a4, a5, a6⟩ := hP
  have hlen : ∀ u (w : slopeLatticeData.FinPl K), (collFam K v m f T Mw hb gG gE).lenN u w = 0 := fun u w =>
    lenSelf0 w (Formalism.HermitianLatticesTheory.idealSmul ((slopeLatticeData.idealPow (tau0 K 2 0) :
      FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : Submodule (𝓞 K) K) (stdLat K (Fin ((T - 2) ^ f))))
  have hlenR : ∀ u (w : slopeLatticeData.FinPl K), (collFam K v m f T Mw hb gG gE).lenR u w = 0 := by
    intro u w
    unfold Fam.lenR
    rw [hlen]
    show (((0 : ℕ) : ℝ) + _ * ((tau0 K 2 0 w : ℤ) : ℝ)) / ramE w = 0
    rw [twist_vector_at_zero]
    simp
  have htR : ∀ w : slopeLatticeData.FinPl K, (collFam K v m f T Mw hb gG gE).tauR w = 0 := by
    intro w
    show ((tau0 K 2 0 w : ℤ) : ℝ) / ramE w = 0
    rw [twist_vector_at_zero]; simp
  refine ⟨a1, a2, fun _ _ => le_rfl, a4, a5, fun u => ?_⟩
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, -, -, -, -, b16, b17, b18⟩ := a6 u
  refine ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, ?_, ?_, le_rfl, ?_, b16, b17, b18⟩
  · intro w _
    have h1 : (collFam K v m f T Mw hb gG gE).lenR u w = 0 := hlenR u w
    have h2 : (collFam K v m f T Mw hb gG gE).tauR w = 0 := htR w
    have h3 : (collFam K v m f T Mw hb gG gE).iop (prBelow w) = 0 := rfl
    rw [h1, h2, h3]; simp
  · intro w _
    have h1 : (collFam K v m f T Mw hb gG gE).lenR u w = 0 := hlenR u w
    have h3 : (collFam K v m f T Mw hb gG gE).lam u = 0 := rfl
    rw [h1, h3]; simp
  · intro (w : slopeLatticeData.FinPl K) _
    show ((tau0 K 2 0 w : ℤ) : ℝ) / ramE w ≤ ∑ j : Fin m, (bump K m gG w + bump K m (gE - gG) w - bump K m gE w)
    rw [twist_vector_at_zero]
    simp [bump_cancel]
end Formalism.LFunctionChainParameters.LChain2
