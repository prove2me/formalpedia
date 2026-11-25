-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LChain2.ev_levelW
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:47:36.821831+00:00
-- url     : https://prove2.me/submissions/ffc9e81e-5c30-454a-a7d1-e4aa4e18a503

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
import Theorems.Thm_Formalism_LFunctionChainParameters_LChain2_phi_card_pos

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
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
namespace Formalism.LFunctionChainParameters.LChain2
theorem _root_.solution (x ε lg : ℝ) (m T : ℕ) (TT T2 : Finset H) (h48 : 48 ≤ x) (hm1 : 1 ≤ m)
    (hLa : 0 ≤ Real.log (aTx x ε) + x ^ (ε / 3)) (hk0 : 0 < ModelText.kTx x ε)
    (hN : NodeSizes T2 (bTx x ε) (bpTx x ε) (ModelText.etaTx x ε) (ModelText.wF x ε m TT T2))
    (heta : ModelText.etaTx x ε + 1 ≤ bTx x ε) (hbpb : bpTx x ε ≤ bTx x ε)
    (hTp : T.Prime) (hT4 : 4 * (PhiSet (H := H)).card ≤ T)
    (hT18 : 18 * ((PhiSet (H := H)).card : ℝ) * x ^ 2 ≤ (T : ℝ))
    (hTlev : 4 * ((PhiSet (H := H)).card : ℝ) / (T : ℝ) * bTx x ε ^ 2
      + ((PhiSet (H := H)).card : ℝ) * Real.log ((T : ℝ) - 1) / ((T : ℝ) - 2) ≤ 1)
    (hlogT : Real.log (T : ℝ) ≤ 4 * x ^ ε)
    (hmlg : (m : ℝ) * lg = Real.log (T : ℝ) - (m : ℝ) * (Real.log 2 + x ^ ε)) :
    LevelWindow (evG x ε lg) evC (ModelText.wF x ε m TT T2) (fun _ => T) := by
  obtain ⟨nz1, nz2, nz3⟩ := hN
  have hx0 : 0 < x := by linarith
  have hb0 : 0 < bTx x ε := Real.exp_pos _
  have hlogb : Real.log (bTx x ε) = x ^ ε := Real.log_exp _
  have hm1r : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
  have hfpos : (0 : ℝ) < ((PhiSet (H := H)).card : ℝ) := by exact_mod_cast (phi_card_pos (H := H))
  have hw2b : ∀ u0 j ρ, InPhi ρ → ModelText.wF x ε m TT T2 u0 j ρ ≤ 2 * bTx x ε := by
    intro u0 j ρ hρ
    by_cases ht : IsThickAt T2 u0 ρ
    · have := (nz2 u0 j ρ ht).2
      linarith
    · have := nz3 u0 j ρ hρ ht
      linarith
  have hlogw : ∀ u0 j (ρ : Fin (PhiSet (H := H)).card),
      Real.log (ModelText.wF x ε m TT T2 u0 j (ePhi ρ) * Real.pi / Real.pi) ≤ Real.log 2 + x ^ ε := by
    intro u0 j ρ
    have hρ : InPhi ((ePhi ρ : PhiSet (H := H)) : E0 × H) := (Finset.mem_filter.1 (ePhi ρ).2).2
    rw [mul_div_assoc, div_self Real.pi_ne_zero, mul_one]
    have := Real.log_le_log (nz1 u0 j _ hρ) (hw2b u0 j _ hρ)
    rwa [Real.log_mul two_ne_zero hb0.ne', hlogb] at this
  intro u0
  refine ⟨hTp, hT4, ?_, hTlev, ?_, ?_⟩
  · show 18 * ((PhiSet (H := H)).card : ℝ) / (x ^ (-(1 : ℝ))) ^ 2 ≤ (T : ℝ)
    rw [Real.rpow_neg_one]
    have : 18 * ((PhiSet (H := H)).card : ℝ) / (x⁻¹) ^ 2 = 18 * ((PhiSet (H := H)).card : ℝ) * x ^ 2 := by
      field_simp
    rw [this]
    exact hT18
  · show (∑ j : Fin m, (1 / ((PhiSet (H := H)).card : ℝ)) * ∑ ρ : Fin (PhiSet (H := H)).card,
        Real.log (ModelText.wF x ε m TT T2 u0 j (ePhi ρ) * Real.pi / Real.pi)) + (m : ℝ) * lg
        - 4 * ((Real.log (aTx x ε) + x ^ (ε / 3)) + (m : ℝ) ^ 2 * (Real.log (aTx x ε) + x ^ (ε / 3))
          / ModelText.kTx x ε) ≤ Real.log (T : ℝ)
    have h1 : ∀ j : Fin m, (1 / ((PhiSet (H := H)).card : ℝ)) * ∑ ρ : Fin (PhiSet (H := H)).card,
        Real.log (ModelText.wF x ε m TT T2 u0 j (ePhi ρ) * Real.pi / Real.pi) ≤ Real.log 2 + x ^ ε := by
      intro j
      have h2' := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin (PhiSet (H := H)).card)))
        fun ρ _ => hlogw u0 j ρ
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h2'
      calc _ ≤ (1 / ((PhiSet (H := H)).card : ℝ)) * (((PhiSet (H := H)).card : ℝ) * (Real.log 2 + x ^ ε)) :=
            mul_le_mul_of_nonneg_left h2' (by positivity)
        _ = Real.log 2 + x ^ ε := by field_simp
    have h3 := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin m))) fun j _ => h1 j
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h3
    have hsl : 0 ≤ 4 * ((Real.log (aTx x ε) + x ^ (ε / 3)) + (m : ℝ) ^ 2 * (Real.log (aTx x ε) + x ^ (ε / 3))
          / ModelText.kTx x ε) := by positivity
    rw [hmlg]
    linarith
  · show Real.log (T : ℝ) ≤ 4 * (m : ℝ) * Real.log (bTx x ε)
    rw [hlogb]
    have h0 : 0 ≤ x ^ ε := Real.rpow_nonneg hx0.le _
    have : 4 * x ^ ε * 1 ≤ 4 * x ^ ε * (m : ℝ) := mul_le_mul_of_nonneg_left hm1r (by positivity)
    linarith
end Formalism.LFunctionChainParameters.LChain2
