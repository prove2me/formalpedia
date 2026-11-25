-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LChain2.model_place
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:07:26.17486+00:00
-- url     : https://prove2.me/submissions/f6dbb62f-a10b-4fe0-97a2-560bcdc4a245

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
import Theorems.Thm_Formalism_LFunctionChainParameters_LChain2_mu_std
import Theorems.Thm_Formalism_LFunctionChainParameters_LChain2_scaled_std
import Theorems.Thm_Formalism_LFunctionChainParameters_LChain2_muMax_incl
import Theorems.Thm_Formalism_LFunctionChainParameters_LChain2_mem_plOver
import Theorems.Thm_Formalism_LFunctionChainParameters_LChain2_twist_vector_apply
import Theorems.Thm_Formalism_LFunctionChainParameters_LChain2_model_card
import Theorems.Thm_Formalism_LFunctionChainParameters_LChain2_lenSelf0
import Theorems.Thm_Formalism_LFunctionChainParameters_LChain2_exists_place
import Theorems.Thm_Formalism_LFunctionChainParameters_LChain2_sum_tau
import Theorems.Thm_Formalism_LFunctionChainParameters_ProjectiveLineModels_standard_lattice_fg
import Theorems.Thm_Formalism_LFunctionChainParameters_ProjectiveLineModels_standard_lattice_span_eq_top
import Theorems.Thm_Formalism_LFunctionChainParameters_slopeLatticeData_idealPow_ne_zero
import Theorems.Thm_Formalism_LFunctionChainParameters_slopeLatticeData_rkK_idealSmul


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
variable (v : InfinitePlace K) (m f T p₁ t₁ Mw : ℕ) (hb : ℝ)
namespace Formalism.LFunctionChainParameters.LChain2
theorem _root_.solution (bb : ℝ) (hm : 1 ≤ m) (hf : 1 ≤ f) (hTp : T.Prime) (hp : p₁.Prime) (hne : p₁ ≠ T)
    (hT4 : 4 * f ≤ T) (hsmall : 4 * (f : ℝ) / (T : ℝ) * bb ^ 2 + dT f T ≤ 1)
    (hTa : 2 * ((t₁ : ℝ) * Real.log (p₁ : ℝ)) ≤ bb ^ 2) :
    (modelFam K v m f T p₁ t₁ Mw hb).PlaceHyp f bb := by
  have hT : 4 ≤ T := by omega
  obtain ⟨ha, hab, hcard⟩ := model_card f T hT
  have hTr : (4 : ℝ) ≤ (T : ℝ) := by exact_mod_cast hT
  have hmemS : ∀ w : slopeLatticeData.FinPl K, w ∈ plOver K p₁ ∪ plOver K T ↔ prBelow w = p₁ ∨ prBelow w = T := by
    intro w
    rw [Finset.mem_union, mem_plOver hp, mem_plOver hTp]
  have hτnn : ∀ w : slopeLatticeData.FinPl K, 0 ≤ tau0 K p₁ t₁ w := by
    intro w
    rw [twist_vector_apply]
    split_ifs
    · positivity
    · exact le_rfl
  have hτR : ∀ w : slopeLatticeData.FinPl K, 0 ≤ (tau0 K p₁ t₁ w : ℝ) / ramE w := fun w =>
    div_nonneg (by exact_mod_cast hτnn w) (ramE_pos w).le
  have hτT : ∀ w : slopeLatticeData.FinPl K, prBelow w = T → tau0 K p₁ t₁ w = 0 := by
    intro w hw
    rw [twist_vector_apply, if_neg]
    intro h
    exact hne (((mem_plOver hp w).1 h).symm.trans hw)
  have hdu : ∀ u, (modelFam K v m f T p₁ t₁ Mw hb).du u = (((T - 2) ^ f : ℕ) : ℝ) := by
    intro u
    show ((Fintype.card (Fin ((T - 2) ^ f)) : ℕ) : ℝ) = _
    rw [Fintype.card_fin]
  have hdM : ∀ u, (modelFam K v m f T p₁ t₁ Mw hb).dM u = (((T - 1) ^ f : ℕ) : ℝ) := by
    intro u
    show ((Fintype.card (Fin ((T - 2) ^ f) ⊕ Fin ((T - 1) ^ f - (T - 2) ^ f)) : ℕ) : ℝ) = _
    rw [hcard]
  have hable : (((T - 2) ^ f : ℕ) : ℝ) ≤ (((T - 1) ^ f : ℕ) : ℝ) := by exact_mod_cast hab
  have hbnn : (0 : ℝ) ≤ (((T - 1) ^ f : ℕ) : ℝ) := Nat.cast_nonneg _
  have hτoff : ∀ w : slopeLatticeData.FinPl K, w ∉ plOver K p₁ ∪ plOver K T → tau0 K p₁ t₁ w = 0 := by
    intro w hw
    rw [twist_vector_apply, if_neg]
    exact fun h => hw (Finset.mem_union_left _ h)
  have hlen : ∀ u (w : slopeLatticeData.FinPl K), (modelFam K v m f T p₁ t₁ Mw hb).lenN u w = 0 := fun u w =>
    lenSelf0 w (Formalism.HermitianLatticesTheory.idealSmul ((slopeLatticeData.idealPow (tau0 K p₁ t₁) :
      FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : Submodule (𝓞 K) K) (stdLat K (Fin ((T - 2) ^ f))))
  have hlenR : ∀ u (w : slopeLatticeData.FinPl K), (modelFam K v m f T p₁ t₁ Mw hb).lenR u w
      = (((T - 2) ^ f : ℕ) : ℝ) * ((tau0 K p₁ t₁ w : ℝ) / ramE w) := by
    intro u w
    unfold Fam.lenR
    rw [hlen, hdu]
    show (((0 : ℕ) : ℝ) + (((T - 2) ^ f : ℕ) : ℝ) * (tau0 K p₁ t₁ w : ℝ)) / ramE w = _
    rw [Nat.cast_zero, zero_add, mul_div_assoc]
  have hrank : (((T - 2) ^ f : ℕ) : ℝ) = (((T - 1) ^ f : ℕ) : ℝ) * (1 - 1 / ((T : ℝ) - 1)) ^ f := by
    have h1 : ((T - 2 : ℕ) : ℝ) = (T : ℝ) - 2 := by
      rw [Nat.cast_sub (by omega)]; norm_num
    have h2 : ((T - 1 : ℕ) : ℝ) = (T : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]; norm_num
    rw [Nat.cast_pow, Nat.cast_pow, h1, h2, ← mul_pow]
    congr 1
    have : (T : ℝ) - 1 ≠ 0 := by linarith
    rw [mul_sub, mul_one, mul_one_div_cancel this]
    ring
  have hoffT : ∀ u (w : slopeLatticeData.FinPl K), (modelFam K v m f T p₁ t₁ Mw hb).lenR u w
      ≤ (modelFam K v m f T p₁ t₁ Mw hb).dM u * ((tau0 K p₁ t₁ w : ℝ) / ramE w + 1) := by
    intro u w
    rw [hlenR, hdM]
    have := hτR w
    nlinarith
  have hovT : ∀ u (w : slopeLatticeData.FinPl K), prBelow w = T → (modelFam K v m f T p₁ t₁ Mw hb).lenR u w
      ≤ (modelFam K v m f T p₁ t₁ Mw hb).dM u * 1 := by
    intro u w hw
    rw [hlenR, hdM, hτT w hw]
    simp
  have hround : ∀ w : slopeLatticeData.FinPl K, (tau0 K p₁ t₁ w : ℝ) / ramE w
      ≤ ∑ _j : Fin m, ((tau0 K p₁ t₁ w : ℝ) / ramE w + 1 + 1 / 2 - 1 / 4) := by
    intro w
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have h1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    have h2 := hτR w
    exact le_trans (by linarith) (le_mul_of_one_le_left (by linarith) h1)
  have hdT : 0 ≤ dT f T := by
    unfold dT
    exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by linarith))) (by linarith)
  have : Nonempty (Fin ((T - 2) ^ f)) := ⟨⟨0, ha⟩⟩
  have hsc := scaled_std K (Fin ((T - 2) ^ f)) (Real.exp (-(dT f T) / 2)) (Real.exp_pos _)
  rw [Real.log_exp] at hsc
  refine ⟨fun w _ => hτnn w, ?_, fun _ _ => zero_le_one, ?_, ?_, fun u => ⟨ProjectiveLineModels.standard_lattice_fg K _,
    ProjectiveLineModels.standard_lattice_span_eq_top K _, ProjectiveLineModels.standard_lattice_fg K _, ProjectiveLineModels.standard_lattice_span_eq_top K _, le_refl _,
    slopeLatticeData.rkK_idealSmul (slopeLatticeData.idealPow_ne_zero _) _, ?_, by exact_mod_cast hT4, ?_, ?_, ?_, ?_, ?_, zero_le_one, ?_, ?_,
    ?_, hsmall⟩⟩
  · exact fun w hw => hτoff w hw
  · intro w hw w' hw'
    rcases (hmemS w).1 hw with h | h
    · exact (hmemS w').2 (Or.inl (hw'.trans h))
    · exact (hmemS w').2 (Or.inr (hw'.trans h))
  · show 2 * ∑ w ∈ plOver K p₁ ∪ plOver K T, lE w * ((tau0 K p₁ t₁ w : ℝ) / ramE w) ≤ bb ^ 2
    rw [sum_tau p₁ t₁ hp _ (fun w hw => (hmemS w).2 (Or.inl hw))]
    exact hTa
  · intro w hw
    exact ⟨hτoff w hw, hlen u w⟩
  · obtain ⟨w, hw⟩ := exists_place (K := K) hTp
    exact Finset.mem_image.2 ⟨w, (hmemS w).2 (Or.inr hw), hw⟩
  · intro w hw
    exact hτT w (Finset.mem_filter.1 hw).2
  · show (modelFam K v m f T p₁ t₁ Mw hb).du u = (modelFam K v m f T p₁ t₁ Mw hb).dM u * (1 - 1 / ((T : ℝ) - 1)) ^ f
    rw [hdu, hdM]
    exact hrank
  · exact fun w _ => hoffT u w
  · exact fun w hw => hovT u w (Finset.mem_filter.1 hw).2
  · exact fun w _ => hround w
  · show muDef (Pi.basisFun K (Fin ((T - 2) ^ f))) (fun _ => ((Real.exp (-(dT f T) / 2) : ℝ) : ℂ) • 1)
        (stdLat K (Fin ((T - 2) ^ f)))
      = muDef (Pi.basisFun K (Fin ((T - 2) ^ f) ⊕ Fin ((T - 1) ^ f - (T - 2) ^ f))) (fun _ => 1) (stdLat K _)
        - dT f T
    rw [hsc.1, mu_std]
    ring
  · show muMaxDef (Pi.basisFun K (Fin ((T - 2) ^ f))) (fun _ => ((Real.exp (-(dT f T) / 2) : ℝ) : ℂ) • 1)
        (stdLat K (Fin ((T - 2) ^ f)))
      ≤ muMaxDef (Pi.basisFun K (Fin ((T - 2) ^ f) ⊕ Fin ((T - 1) ^ f - (T - 2) ^ f))) (fun _ => 1) (stdLat K _)
    rw [hsc.2]
    have := muMax_incl K (Fin ((T - 2) ^ f)) (Fin ((T - 1) ^ f - (T - 2) ^ f))
    linarith
end Formalism.LFunctionChainParameters.LChain2
