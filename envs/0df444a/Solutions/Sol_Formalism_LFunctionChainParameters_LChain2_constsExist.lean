-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LChain2.constsExist
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T02:50:50.568835+00:00
-- url     : https://prove2.me/submissions/83099769-7ec8-40e3-9abc-23f688c15599

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
import Theorems.Thm_Formalism_LFunctionChainParameters_LChain2_absorb1
import Theorems.Thm_Formalism_LFunctionChainParameters_LChain2_absorb2
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_Facts_n1


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
theorem _root_.solution {U0 : Type} [Fintype U0] {W : U0 → Type} [∀ u0, Fintype (W u0)] {Top : Type} [Fintype Top]
    {m f : ℕ} (Dd : Data U0 W Top m f) (eDiv eLoss cHH c0 : ℝ)
    (hx : 0 < Dd.x) (hnT : 0 < Dd.nT) (ha : 0 < Dd.a) (hLa : 0 < Dd.La) (hm : 1 ≤ m) (hB0 : 0 < Dd.B0)
    (hNc : 0 ≤ Dd.Nc) (hb : 0 < Dd.b) (hL : 0 < Dd.L) (hk : 1 ≤ Dd.k) (hT : ∀ u0 u, 1 ≤ Dd.T u0 u)
    (hhw : ∀ u0 u u', Dd.h u0 u = Dd.h u0 u') (hTw : ∀ u0 u u', Dd.T u0 u = Dd.T u0 u') :
    ∃ cDiv cE cCount cSlope cLoss : ℝ, 0 ≤ cDiv ∧ 0 ≤ cE ∧ 0 ≤ cCount ∧ 0 ≤ cSlope ∧ 0 ≤ cLoss ∧
      Dd.DIV ⟨cDiv, eDiv, cE, 0, cCount, cSlope, c0, cLoss, eLoss, cHH⟩ ∧
      EComp5 Dd ⟨cDiv, eDiv, cE, 0, cCount, cSlope, c0, cLoss, eLoss, cHH⟩ ∧
      Dd.HComp ⟨cDiv, eDiv, cE, 0, cCount, cSlope, c0, cLoss, eLoss, cHH⟩ ∧
      Count5 Dd ⟨cDiv, eDiv, cE, 0, cCount, cSlope, c0, cLoss, eLoss, cHH⟩ ∧
      Dd.Slopes ⟨cDiv, eDiv, cE, 0, cCount, cSlope, c0, cLoss, eLoss, cHH⟩ ∧
      LossBounds Dd ⟨cDiv, eDiv, cE, 0, cCount, cSlope, c0, cLoss, eLoss, cHH⟩ := by
  have hmr : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hk0 : 0 < Dd.k := by linarith
  have hP1 : 0 < Dd.nT * Dd.a * Dd.La := mul_pos (mul_pos hnT ha) hLa
  have hP2 : 0 < (m : ℝ) * Dd.B0 := mul_pos (by linarith) hB0
  have hP5 : 0 < Dd.nT * (m : ℝ) * Dd.b * Dd.x ^ (eLoss * Dd.ε) :=
    mul_pos (mul_pos (mul_pos hnT (by linarith)) hb) (Real.rpow_pos_of_pos hx _)
  set S1 := ∑ u0, ∑ u : W u0, |Dd.muCC u0 + Dd.h u0 u - Dd.Fo u0
    - ∑ t, ((m : ℝ) * (ph (Dd.aT t) - Dd.aT t * Dd.logOm) - Dd.aT t * Real.log (Dd.T u0 u))| with hS1
  set S2 := ∑ u0, ∑ u : W u0, |Dd.Ee u0 u - (m : ℝ) * Dd.sumA * Dd.lg| with hS2
  set S3 := ∑ u0, |(∑ j : Fin m, (1 / (f : ℝ)) * ∑ ρ : Fin f, Real.log (Dd.w u0 j ρ * Dd.v / Real.pi))
    + (m : ℝ) * Dd.lg| with hS3
  set S4 := ∑ u0, ∑ u : W u0, |Real.log (Dd.T u0 u)| with hS4
  set S5 := ∑ u0, ∑ u : W u0, |Dd.muM u0 u| with hS5
  set S6 := ∑ u0, ∑ u : W u0, |Dd.muMaxM u0 u| with hS6
  set S7 := ∑ u0, |Dd.ASK u0 - Dd.Ga u0| with hS7
  set S8 := ∑ u0, |Dd.IO u0| with hS8
  have n1 : 0 ≤ S1 := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  have n2 : 0 ≤ S2 := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  have n3 : 0 ≤ S3 := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have n4 : 0 ≤ S4 := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  have n5 : 0 ≤ S5 := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  have n6 : 0 ≤ S6 := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  have n7 : 0 ≤ S7 := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have n8 : 0 ≤ S8 := Finset.sum_nonneg fun _ _ => abs_nonneg _
  refine ⟨S1 / (Dd.nT * Dd.a * Dd.La), S2 / ((m : ℝ) * Dd.B0), S3 / Dd.La + S4 / Dd.L,
    (S5 + S6) / (Dd.nT * Dd.a * Dd.La), (S7 + S8) / (Dd.nT * (m : ℝ) * Dd.b * Dd.x ^ (eLoss * Dd.ε)),
    by positivity, by positivity, by positivity, by positivity, by positivity, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro u0 u
    show Dd.muCC u0 + Dd.h u0 u - Dd.Fo u0 ≤
      (∑ t, ((m : ℝ) * (ph (Dd.aT t) - Dd.aT t * Dd.logOm) - Dd.aT t * Real.log (Dd.T u0 u)))
        + S1 / (Dd.nT * Dd.a * Dd.La) * Dd.nT * Dd.a * Dd.La
        + S1 / (Dd.nT * Dd.a * Dd.La) * (m : ℝ) * (Dd.B0 + Dd.Nc) * Dd.x ^ (eDiv * Dd.ε)
    have h1 := le_trans (le_abs_self _) (absorb2 (fun (u0 : U0) (u : W u0) => Dd.muCC u0 + Dd.h u0 u - Dd.Fo u0
      - ∑ t, ((m : ℝ) * (ph (Dd.aT t) - Dd.aT t * Dd.logOm) - Dd.aT t * Real.log (Dd.T u0 u))) u0 u)
    have h2 : S1 / (Dd.nT * Dd.a * Dd.La) * Dd.nT * Dd.a * Dd.La = S1 := by
      calc _ = S1 / (Dd.nT * Dd.a * Dd.La) * (Dd.nT * Dd.a * Dd.La) := by ring
        _ = S1 := div_mul_cancel₀ _ hP1.ne'
    have h3 : 0 ≤ S1 / (Dd.nT * Dd.a * Dd.La) * (m : ℝ) * (Dd.B0 + Dd.Nc) * Dd.x ^ (eDiv * Dd.ε) := by
      have : 0 < Dd.x ^ (eDiv * Dd.ε) := Real.rpow_pos_of_pos hx _
      positivity
    rw [h2]
    linarith
  · intro u0 u
    show |Dd.Ee u0 u - (m : ℝ) * Dd.sumA * Dd.lg| ≤ S2 / ((m : ℝ) * Dd.B0) * (m : ℝ) * Dd.B0
    have h2 : S2 / ((m : ℝ) * Dd.B0) * (m : ℝ) * Dd.B0 = S2 := by
      calc _ = S2 / ((m : ℝ) * Dd.B0) * ((m : ℝ) * Dd.B0) := by ring
        _ = S2 := div_mul_cancel₀ _ hP2.ne'
    rw [h2]
    exact absorb2 (fun (u0 : U0) (u : W u0) => Dd.Ee u0 u - (m : ℝ) * Dd.sumA * Dd.lg) u0 u
  · intro u0 u u'
    rw [hhw u0 u u', hTw u0 u u', sub_self, abs_zero]
    show (0 : ℝ) ≤ 0 * _
    rw [zero_mul]
  · intro u0 u
    have hc : 0 ≤ S3 / Dd.La + S4 / Dd.L := by positivity
    have hlog : 0 ≤ Real.log (Dd.T u0 u) := Real.log_nonneg (hT u0 u)
    refine ⟨?_, ?_, fun u' => ?_⟩
    · show (∑ j : Fin m, (1 / (f : ℝ)) * ∑ ρ : Fin f, Real.log (Dd.w u0 j ρ * Dd.v / Real.pi)) + (m : ℝ) * Dd.lg
        - (S3 / Dd.La + S4 / Dd.L) * (Dd.La + (m : ℝ) ^ 2 * Dd.La / Dd.k) ≤ Real.log (Dd.T u0 u)
      have h1 := le_trans (le_abs_self _) (absorb1 (fun u0 : U0 =>
        (∑ j : Fin m, (1 / (f : ℝ)) * ∑ ρ : Fin f, Real.log (Dd.w u0 j ρ * Dd.v / Real.pi)) + (m : ℝ) * Dd.lg) u0)
      have h2 : S3 ≤ (S3 / Dd.La + S4 / Dd.L) * (Dd.La + (m : ℝ) ^ 2 * Dd.La / Dd.k) := by
        have e1 : S3 = S3 / Dd.La * Dd.La := (div_mul_cancel₀ _ hLa.ne').symm
        have e2 : 0 ≤ S3 / Dd.La * ((m : ℝ) ^ 2 * Dd.La / Dd.k) := by positivity
        have e3 : 0 ≤ S4 / Dd.L * (Dd.La + (m : ℝ) ^ 2 * Dd.La / Dd.k) := by positivity
        nlinarith
      linarith
    · show Real.log (Dd.T u0 u) ≤ (S3 / Dd.La + S4 / Dd.L) * (m : ℝ) * Dd.L
      have h1 := le_trans (le_abs_self _) (absorb2 (fun (u0 : U0) (u : W u0) => Real.log (Dd.T u0 u)) u0 u)
      have e1 : S4 = S4 / Dd.L * Dd.L := (div_mul_cancel₀ _ hL.ne').symm
      have e2 : S4 / Dd.L * Dd.L ≤ (S3 / Dd.La + S4 / Dd.L) * (m : ℝ) * Dd.L := by
        have e3 : S4 / Dd.L ≤ (S3 / Dd.La + S4 / Dd.L) * (m : ℝ) := by
          have e4 : 0 ≤ S3 / Dd.La := by positivity
          have e5 : 0 ≤ S4 / Dd.L := by positivity
          nlinarith
        exact mul_le_mul_of_nonneg_right e3 hL.le
      linarith
    · rw [hTw u0 u u', sub_self, abs_zero]
      exact mul_nonneg hc (Real.log_nonneg hk)
  · intro u0 u
    have h5 := absorb2 (fun (u0 : U0) (u : W u0) => Dd.muM u0 u) u0 u
    have h6 := absorb2 (fun (u0 : U0) (u : W u0) => Dd.muMaxM u0 u) u0 u
    have h2 : (S5 + S6) / (Dd.nT * Dd.a * Dd.La) * Dd.nT * Dd.a * Dd.La = S5 + S6 := by
      calc _ = (S5 + S6) / (Dd.nT * Dd.a * Dd.La) * (Dd.nT * Dd.a * Dd.La) := by ring
        _ = S5 + S6 := div_mul_cancel₀ _ hP1.ne'
    constructor
    · show -((S5 + S6) / (Dd.nT * Dd.a * Dd.La) * Dd.nT * Dd.a * Dd.La * (1 + (m : ℝ) / Dd.k)) ≤ Dd.muM u0 u
      rw [h2]
      have e1 : 0 ≤ (S5 + S6) * ((m : ℝ) / Dd.k) := by positivity
      have e2 := neg_abs_le (Dd.muM u0 u)
      nlinarith
    · show Dd.muMaxM u0 u ≤ (S5 + S6) / (Dd.nT * Dd.a * Dd.La) * Dd.nT * Dd.a * Dd.La
      rw [h2]
      have e2 := le_abs_self (Dd.muMaxM u0 u)
      linarith
  · intro u0
    have h2 : Dd.LoP ⟨S1 / (Dd.nT * Dd.a * Dd.La), eDiv, S2 / ((m : ℝ) * Dd.B0), 0, S3 / Dd.La + S4 / Dd.L,
        (S5 + S6) / (Dd.nT * Dd.a * Dd.La), c0,
        (S7 + S8) / (Dd.nT * (m : ℝ) * Dd.b * Dd.x ^ (eLoss * Dd.ε)), eLoss, cHH⟩ = S7 + S8 := by
      show (S7 + S8) / (Dd.nT * (m : ℝ) * Dd.b * Dd.x ^ (eLoss * Dd.ε)) * Dd.nT * (m : ℝ) * Dd.b
        * Dd.x ^ (eLoss * Dd.ε) = S7 + S8
      calc _ = (S7 + S8) / (Dd.nT * (m : ℝ) * Dd.b * Dd.x ^ (eLoss * Dd.ε))
            * (Dd.nT * (m : ℝ) * Dd.b * Dd.x ^ (eLoss * Dd.ε)) := by ring
        _ = S7 + S8 := div_mul_cancel₀ _ hP5.ne'
    rw [h2]
    have h7 := le_trans (le_abs_self _) (absorb1 (fun u0 : U0 => Dd.ASK u0 - Dd.Ga u0) u0)
    have h8 := le_trans (le_abs_self _) (absorb1 (fun u0 : U0 => Dd.IO u0) u0)
    exact ⟨by linarith, by linarith⟩
end Formalism.LFunctionChainParameters.LChain2
