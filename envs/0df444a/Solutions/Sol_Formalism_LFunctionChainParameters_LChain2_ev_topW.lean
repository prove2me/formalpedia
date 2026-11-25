-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LChain2.ev_topW
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:07:22.016651+00:00
-- url     : https://prove2.me/submissions/bcd036ec-0165-49ae-a6a4-a1e8e7f665ed

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
import Theorems.Thm_Formalism_LFunctionChainParameters_LChain2_ev_wF_pos
import Theorems.Thm_P2M_Formalism_LFunctionChainParameters_LChain2_ev_top_arith__f0d0f1ee58a0
import Theorems.Thm_Formalism_LFunctionChainParameters_LChain_ModelEv_askDA_le


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
theorem _root_.solution (x ε lg : ℝ) (m T N : ℕ) (TT T2 : Finset H) (h48 : 48 ≤ x) (hlx : 4 ≤ Real.log x)
    (hLa : 0 ≤ Real.log (aTx x ε) + x ^ (ε / 3)) (hk0 : 0 < ModelText.kTx x ε)
    (hmlg : (m : ℝ) * lg = Real.log (T : ℝ) - (m : ℝ) * (Real.log 2 + x ^ ε)) :
    TopAtLevel Model.DA (fun _ => 0) (evG x ε lg) evC N TT T2
      (fun _ => aTx x ε) (ModelText.wF x ε m TT T2) (fun _ => T) := by
  have hx0 : 0 < x := by linarith
  have hb0 : 0 < bTx x ε := Real.exp_pos _
  have hlogb : Real.log (bTx x ε) = x ^ ε := Real.log_exp _
  have ha0 : 0 < aTx x ε := mul_pos hx0 hb0
  have hloga : Real.log (aTx x ε) = Real.log x + x ^ ε := by
    unfold aTx; rw [Real.log_mul hx0.ne' hb0.ne', hlogb]
  intro u0
  have hL : (∑ t ∈ TT, ∑ j : Fin m, ASK Model.DA N (aTx x ε) t
      (ModelText.wF x ε m TT T2 u0 j)) ≤ (TT.card : ℝ) * ((m : ℝ) * aTx x ε) := by
    calc _ ≤ ∑ _t ∈ TT, ∑ _j : Fin m, aTx x ε := Finset.sum_le_sum fun t _ => Finset.sum_le_sum fun j _ =>
          ModelEv.askDA_le _ _ _ _ ha0.le (fun ρ => (ev_wF_pos x ε m TT T2 hx0 u0 j ρ).le)
      _ = _ := by simp [Finset.sum_const, nsmul_eq_mul]
  refine le_trans hL (le_add_of_le_of_nonneg (le_add_of_le_of_nonneg ?_ ?_) ?_)
  · show (TT.card : ℝ) * ((m : ℝ) * aTx x ε) ≤
      (∑ _t : TT, ((m : ℝ) * (ph (aTx x ε) - aTx x ε * (Real.eulerMascheroniConstant + Real.log (Real.pi / Real.pi)
          - (0 : ℂ).re)) - aTx x ε * Real.log (T : ℝ))) + (m : ℝ) * (∑ _t : TT, aTx x ε) * lg
    rw [Finset.sum_const, Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul, nsmul_eq_mul,
      div_self Real.pi_ne_zero, Real.log_one, Complex.zero_re, add_zero, sub_zero]
    unfold ph
    refine ev_top_arith' _ _ _ _ _ _ _ (Real.log x) (x ^ ε) (Real.log 2) (Nat.cast_nonneg _) (Nat.cast_nonneg _) ha0.le
      hmlg hloga ?_
    have h1 := Real.eulerMascheroniConstant_lt_two_thirds
    have h2 : Real.log 2 ≤ 2 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
    linarith
  · exact mul_nonneg (mul_nonneg (mul_nonneg zero_le_one (Nat.cast_nonneg _)) ha0.le) hLa
  · show 0 ≤ (1 : ℝ) * (m : ℝ) * ((2 * (Fintype.card H : ℝ)) * m * bTx x ε * x ^ ε
          + (T2.card : ℝ) * ModelText.kTx x ε * bTx x ε * x ^ ε
            / ((Fintype.card H : ℝ) * ((Fintype.card H : ℝ) * x ^ (-ε)))) * x ^ ((1 : ℝ) * ε)
    positivity
end Formalism.LFunctionChainParameters.LChain2
