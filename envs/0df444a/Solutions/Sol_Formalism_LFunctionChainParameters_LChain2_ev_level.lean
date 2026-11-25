-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LChain2.ev_level
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:55:29.902385+00:00
-- url     : https://prove2.me/submissions/13b330c9-3ed4-44af-9052-2db242cc89ff

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
open Formalism.LFunctionChainParameters.ProjectiveLineModels (stdLat inclMat)
namespace Formalism.LFunctionChainParameters.LChain2
theorem _root_.solution (f T : ℕ) (bb : ℝ) (hf : 1 ≤ f) (h1 : (64 * (f : ℝ) ^ 2 + 5 : ℝ) ≤ (T : ℝ))
    (h2 : 8 * (f : ℝ) * bb ^ 2 ≤ (T : ℝ)) :
    4 * (f : ℝ) / (T : ℝ) * bb ^ 2 + (f : ℝ) * Real.log ((T : ℝ) - 1) / ((T : ℝ) - 2) ≤ 1 := by
  have hfr : (1 : ℝ) ≤ (f : ℝ) := by exact_mod_cast hf
  have hTpos : (0 : ℝ) < (T : ℝ) := by nlinarith
  have hA : 4 * (f : ℝ) / (T : ℝ) * bb ^ 2 ≤ 1 / 2 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hTpos]
    linarith
  set y : ℝ := (T : ℝ) - 1 with hy
  have hy1 : 64 * (f : ℝ) ^ 2 + 4 ≤ y := by rw [hy]; linarith
  have hypos : 0 < y := by nlinarith
  have hs : 8 * (f : ℝ) ≤ Real.sqrt y := by
    rw [show 8 * (f : ℝ) = Real.sqrt ((8 * (f : ℝ)) ^ 2) from (Real.sqrt_sq (by positivity)).symm]
    exact Real.sqrt_le_sqrt (by nlinarith)
  have hspos : 0 < Real.sqrt y := Real.sqrt_pos.2 hypos
  have hlog : Real.log y ≤ 2 * Real.sqrt y := by
    have h4 := Real.log_le_sub_one_of_pos hspos
    have h5 : Real.log y = 2 * Real.log (Real.sqrt y) := by
      rw [Real.log_sqrt hypos.le]; ring
    rw [h5]; linarith
  have hsq : Real.sqrt y * Real.sqrt y = y := Real.mul_self_sqrt hypos.le
  have hB : (f : ℝ) * Real.log y / ((T : ℝ) - 2) ≤ 1 / 2 := by
    have hden : 0 < (T : ℝ) - 2 := by nlinarith
    rw [div_le_iff₀ hden]
    have h6 : (T : ℝ) - 2 = y - 1 := by rw [hy]; ring
    rw [h6]
    have h7 : (f : ℝ) * Real.log y ≤ (f : ℝ) * (2 * Real.sqrt y) :=
      mul_le_mul_of_nonneg_left hlog (by linarith)
    have h8 : (f : ℝ) * (2 * Real.sqrt y) ≤ Real.sqrt y * Real.sqrt y / 4 := by nlinarith
    rw [hsq] at h8
    nlinarith
  linarith
end Formalism.LFunctionChainParameters.LChain2
