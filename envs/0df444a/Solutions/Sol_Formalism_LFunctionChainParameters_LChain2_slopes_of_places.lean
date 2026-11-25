-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LChain2.slopes_of_places
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:58:51.463896+00:00
-- url     : https://prove2.me/submissions/0e3cf4ed-89ca-4930-80c2-4a5a0dcf0079

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
import Theorems.Thm_Formalism_LFunctionChainParameters_LChain2_ramE_pos
import Theorems.Thm_Formalism_LFunctionChainParameters_LChain2_lE_nonneg
import Theorems.Thm_Formalism_LFunctionChainParameters_LChain2_sum_log_norm_over_prime
import Theorems.Thm_Formalism_LFunctionChainParameters_LChain2_prBelow_prime
import Theorems.Thm_Formalism_LFunctionChainParameters_LChain2_Fam_slopeRel
import Theorems.Thm_Formalism_LFunctionChainParameters_LChain2_phi_card_pos
import Theorems.Thm_Formalism_LFunctionChainParameters_LatticeToWeightTransfer_unit_weight_of_primitive


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
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H] {W : H → Type} [∀ u0, Fintype (W u0)] {m : ℕ}
variable [∀ u0, Nonempty (W u0)]
namespace Formalism.LFunctionChainParameters.LChain2
theorem _root_.solution : SlopesOfPlaces (H := H) (W := W) (m := m) := by
  intro G C cT D ell N TT T2 a w Fm hx hk hX hd hP hS u0 u
  obtain ⟨h4, hcT, hsz⟩ := hS
  have hf : (1 : ℝ) ≤ ((PhiSet (H := H)).card : ℝ) := by exact_mod_cast phi_card_pos (H := H)
  have hb : 0 < bTx G.x G.ε := Real.exp_pos _
  have hHyp : LatticeToWeightTransfer.HypPrim (restr (mkData G C.cHH D ell N TT T2 a w Fm) u0)
      (fun _ u => (Fm u0).prim u) := by
    intro _ u
    have hrel := (Fm u0).slopeRel u _ _ (hX u0 u) (hd u0 u) (hP u0)
    obtain ⟨hτ, hτ0, hio, hsat, hTa, hu⟩ := hP u0
    obtain ⟨hFG, hspan, -, -, hle, hrkN, hoff, hT4, hTPr, hτT, hrank, hoffT, hovT, hlam, hround, hMu, hMaxMu,
      hsmall⟩ := hu u
    have hunit : ∀ p ∈ (Fm u0).Pr,
        ∑ w ∈ (Fm u0).S.filter (fun w => prBelow w = p), lE w = Real.log (p : ℝ) := by
      intro p hp
      obtain ⟨w0, hw0, rfl⟩ := Finset.mem_image.1 hp
      exact sum_log_norm_over_prime _ _ (prBelow_prime w0) (fun w' hw' => hsat w0 hw0 w' hw')
    have hdM : 0 < (Fm u0).dM u := by
      have h0 : 0 ≤ (Fm u0).dM u := Nat.cast_nonneg _
      rcases h0.lt_or_eq with h | h
      · exact h
      · have := hd u0 u
        rw [hrank, ← h, zero_mul] at this
        exact absurd this (lt_irrefl _)
    refine ⟨fun w _ => lE_nonneg w, hdM, ?_, hT4, hrank, Finset.filter_subset _ _, ?_, ?_, hio, hoffT, hovT,
      hlam, hunit _ hTPr, hround, le_refl _, hrel.2, hrel.1, hMu, hMaxMu, hTa, hsmall, ?_, hunit,
      fun _ _ => rfl⟩
    · show (2 : ℝ) < ((Fm u0).T u : ℝ)
      linarith
    · intro w hw
      show ((Fm u0).τ w : ℝ) / ramE w = 0
      rw [hτT w hw]; simp
    · intro w hw
      exact div_nonneg (by exact_mod_cast hτ w hw) (ramE_pos w).le
    · intro w hw
      exact Finset.mem_image_of_mem _ hw
  have hId : LatticeToWeightTransfer.PlaceSumIdentities (restr (mkData G C.cHH D ell N TT T2 a w Fm) u0)
      (LatticeToWeightTransfer.toP (restr (mkData G C.cHH D ell N TT T2 a w Fm) u0) (fun _ u => (Fm u0).prim u)) :=
    fun _ _ => ⟨rfl, rfl, fun _ => rfl⟩
  have hSz : LatticeToWeightTransfer.SizesPrim (restr (mkData G C.cHH D ell N TT T2 a w Fm) u0) C (XppH H G) cT
      (fun _ u => (Fm u0).prim u) := by
    refine ⟨h4, hcT, ?_, ?_, fun _ u => ⟨le_refl _, ?_, (hsz u0 u).2⟩⟩
    · show 0 ≤ (m : ℝ) * ((2 * (Fintype.card H : ℝ)) * m * bTx G.x G.ε * G.x ^ G.ε)
      have := Real.rpow_nonneg hx.le G.ε
      positivity
    · show 0 ≤ aTx G.x G.ε / G.k + bpTx G.x G.ε
      have h1 : 0 < aTx G.x G.ε := mul_pos hx hb
      have h2 : 0 < XpTx G.x G.ε := Real.exp_pos _
      unfold bpTx
      positivity
    · have := (hsz u0 u).1
      show (Fm u0).lam u ≤ cT * ((Fintype.card TT : ℕ) : ℝ) * (m : ℝ) * (aTx G.x G.ε / G.k + bpTx G.x G.ε)
      rwa [Fintype.card_coe]
  exact LatticeToWeightTransfer.unit_weight_of_primitive _ C (XppH H G) cT _ hHyp hId hSz () u
end Formalism.LFunctionChainParameters.LChain2
