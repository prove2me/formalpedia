-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LChain2.levelPrime
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:08:03.732329+00:00
-- url     : https://prove2.me/submissions/969398c3-4ed8-4675-9755-719fe51993dd

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
namespace Formalism.LFunctionChainParameters.LChain2
theorem _root_.solution (f : ℕ) (bb : ℝ) (hf : 1 ≤ f) (n0 : ℕ) :
    ∃ T : ℕ, T.Prime ∧ n0 ≤ T ∧ 4 * f ≤ T ∧
      4 * (f : ℝ) / (T : ℝ) * bb ^ 2 + (f : ℝ) * Real.log ((T : ℝ) - 1) / ((T : ℝ) - 2) ≤ 1 := by
  obtain ⟨T, hTge, hTp⟩ := Nat.exists_infinite_primes (n0 + 64 * f ^ 2 + ⌈8 * (f : ℝ) * bb ^ 2⌉₊ + 5)
  have hfr : (1 : ℝ) ≤ (f : ℝ) := by exact_mod_cast hf
  have h1 : (64 * (f : ℝ) ^ 2 + 5 : ℝ) ≤ (T : ℝ) := by
    have : 64 * f ^ 2 + 5 ≤ T := by omega
    exact_mod_cast this
  have h2 : 8 * (f : ℝ) * bb ^ 2 ≤ (T : ℝ) := by
    have h3 : (⌈8 * (f : ℝ) * bb ^ 2⌉₊ : ℝ) ≤ (T : ℝ) := by
      have : ⌈8 * (f : ℝ) * bb ^ 2⌉₊ ≤ T := by omega
      exact_mod_cast this
    exact le_trans (Nat.le_ceil _) h3
  have hTpos : (0 : ℝ) < (T : ℝ) := by nlinarith
  refine ⟨T, hTp, by omega, ?_, ?_⟩
  · have : 4 * f ≤ 64 * f ^ 2 := by nlinarith
    omega
  · have hA : 4 * (f : ℝ) / (T : ℝ) * bb ^ 2 ≤ 1 / 2 := by
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
