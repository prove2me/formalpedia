-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LChain2.ev_prime
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T02:39:55.088937+00:00
-- url     : https://prove2.me/submissions/8a4ed861-ac2c-4966-a508-f242dcc110a4

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
import Theorems.Thm_Formalism_LFunctionChainParameters_LChain2_ev_level

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
theorem _root_.solution (f : ℕ) (x b : ℝ) (hf : 1 ≤ f) (hx : 1 ≤ x) (hE : 100 * (f : ℝ) ^ 2 * x ^ 2 ≤ b) :
    ∃ T : ℕ, T.Prime ∧ 4 * f ≤ T ∧ 18 * (f : ℝ) * x ^ 2 ≤ (T : ℝ) ∧
      4 * (f : ℝ) / (T : ℝ) * b ^ 2 + (f : ℝ) * Real.log ((T : ℝ) - 1) / ((T : ℝ) - 2) ≤ 1 ∧ (T : ℝ) ≤ b ^ 4 := by
  have hfr : (1 : ℝ) ≤ (f : ℝ) := by exact_mod_cast hf
  have hx2 : 1 ≤ x ^ 2 := one_le_pow₀ hx
  have hf2 : (f : ℝ) ≤ (f : ℝ) ^ 2 := by nlinarith
  have hfx : (f : ℝ) ^ 2 ≤ (f : ℝ) ^ 2 * x ^ 2 := le_mul_of_one_le_right (by positivity) hx2
  have hfx' : (f : ℝ) * x ^ 2 ≤ (f : ℝ) ^ 2 * x ^ 2 := mul_le_mul_of_nonneg_right hf2 (by positivity)
  have hb100 : 100 ≤ b := by nlinarith
  obtain ⟨M, hM⟩ : ∃ M : ℕ, M = 64 * f ^ 2 + ⌈8 * (f : ℝ) * b ^ 2⌉₊ + ⌈18 * (f : ℝ) * x ^ 2⌉₊ + 5 := ⟨_, rfl⟩
  obtain ⟨T, hTp, hlt, hle⟩ := Nat.exists_prime_lt_and_le_two_mul M (by omega)
  have c1 : (⌈8 * (f : ℝ) * b ^ 2⌉₊ : ℝ) < 8 * (f : ℝ) * b ^ 2 + 1 := Nat.ceil_lt_add_one (by positivity)
  have c2 : (⌈18 * (f : ℝ) * x ^ 2⌉₊ : ℝ) < 18 * (f : ℝ) * x ^ 2 + 1 := Nat.ceil_lt_add_one (by positivity)
  have d1 : 8 * (f : ℝ) * b ^ 2 ≤ (⌈8 * (f : ℝ) * b ^ 2⌉₊ : ℝ) := Nat.le_ceil _
  have d2 : 18 * (f : ℝ) * x ^ 2 ≤ (⌈18 * (f : ℝ) * x ^ 2⌉₊ : ℝ) := Nat.le_ceil _
  have hMr : (M : ℝ) = 64 * (f : ℝ) ^ 2 + (⌈8 * (f : ℝ) * b ^ 2⌉₊ : ℝ) + (⌈18 * (f : ℝ) * x ^ 2⌉₊ : ℝ) + 5 := by
    rw [hM]; push_cast; ring
  have hTM : (M : ℝ) ≤ (T : ℝ) := by exact_mod_cast hlt.le
  have hT2M : (T : ℝ) ≤ 2 * (M : ℝ) := by exact_mod_cast hle
  have p1 : (0 : ℝ) ≤ 8 * (f : ℝ) * b ^ 2 := by positivity
  have p2 : (0 : ℝ) ≤ 18 * (f : ℝ) * x ^ 2 := by positivity
  have p3 : (0 : ℝ) ≤ 64 * (f : ℝ) ^ 2 := by positivity
  refine ⟨T, hTp, ?_, by linarith, ev_level f T b hf (by linarith) (by linarith), ?_⟩
  · have : 4 * f ≤ 64 * f ^ 2 := by nlinarith
    omega
  · have hb0 : 0 < b := by linarith
    have e1 : 8 * (f : ℝ) * b ^ 2 ≤ b ^ 3 := by
      have : 8 * (f : ℝ) ≤ b := by nlinarith
      calc 8 * (f : ℝ) * b ^ 2 ≤ b * b ^ 2 := mul_le_mul_of_nonneg_right this (by positivity)
        _ = b ^ 3 := by ring
    have e2 : b ≤ b ^ 3 := by
      have : 1 ≤ b ^ 2 := one_le_pow₀ (by linarith)
      calc b = b * 1 := by ring
        _ ≤ b * b ^ 2 := mul_le_mul_of_nonneg_left this hb0.le
        _ = b ^ 3 := by ring
    have e3 : 100 * b ^ 3 ≤ b ^ 4 := by
      calc 100 * b ^ 3 ≤ b * b ^ 3 := mul_le_mul_of_nonneg_right hb100 (by positivity)
        _ = b ^ 4 := by ring
    have e4 : 0 < b ^ 3 := by positivity
    nlinarith
end Formalism.LFunctionChainParameters.LChain2
