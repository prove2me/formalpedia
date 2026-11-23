-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LBrDiv.construct_parameter_definitions
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:03:00.936611+00:00
-- url     : https://prove2.me/submissions/8ac30459-a663-4333-90b2-e0123a6f647c

import Definitions.Def_Formalism_SizeWindowBrackets_SBrDiv
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_LevelOfCongruence
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_StronglyIrreducible
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DualPl
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SizeMu
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_Rerealize
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_PBrDiv
import Theorems.Thm_Formalism_D5_Bal_card_G_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open Formalism.HN
noncomputable section
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.LBrDiv
open Formalism Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.LErr Formalism.LFunctionChainParameters.LChain2
namespace Formalism.LFunctionChainParameters.LBrDiv
theorem _root_.solution : MkParDefs := by
  intro H _ _ _ W _ m G cHH D ell N TT T2 a w Fm
  have hL : (mkData G cHH D ell N TT T2 a w Fm).L = G.x ^ G.ε := by
    show Real.log (bTx G.x G.ε) = _
    unfold bTx
    rw [Real.log_exp]
  refine ⟨hL, ?_, rfl, rfl, ?_, ?_, ?_⟩
  · rw [hL]; rfl
  · have h1 : (Fintype.card (E0 × H) : ℂ) = 2 * ((PhiSet (H := H)).card : ℂ) := Formalism.D5.Bal.card_G_eq
    have h2 : Fintype.card (E0 × H) = 2 * (PhiSet (H := H)).card := by exact_mod_cast h1
    have h3 : Fintype.card (E0 × H) = 4 * Fintype.card H := by
      simp [Fintype.card_prod]
    have h4 : (PhiSet (H := H)).card = 2 * Fintype.card H := by omega
    exact_mod_cast h4
  · intro hx hk
    show 0 ≤ (T2.card : ℝ) * G.k * bTx G.x G.ε * G.x ^ G.ε
      / ((Fintype.card H : ℝ) * ((Fintype.card H : ℝ) * G.x ^ (-G.ε)))
    have hb : 0 ≤ bTx G.x G.ε := (Real.exp_pos _).le
    exact div_nonneg
      (mul_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hk) hb) (Real.rpow_nonneg hx _))
      (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg hx _)))
  · show (Fintype.card TT : ℝ) = _
    rw [Fintype.card_coe]
end Formalism.LFunctionChainParameters.LBrDiv
