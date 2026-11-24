-- Prove2me | solution 1 for Formalism.L2.Th1.D.biextension_hypotheses_of_conditions
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:37:22.334744+00:00
-- url     : https://prove2.me/submissions/97f10bb5-5b8b-42a9-aafe-6d6c52432049

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_LetterShift
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FinalS
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_Transfer
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_BiextensionHypothesesOfConditions
import Theorems.Thm_Formalism_L2_Th1_D_B4_simeq_sum_zero
import Theorems.Thm_Formalism_L2_Th1_D_B4_subst_C_mul_sum
import Theorems.Thm_Formalism_L2_Th1_D_B4_first_difference_C_mul_sum
import Theorems.Thm_Formalism_L2_Th1_D_B4_second_difference_C_mul_sum
import Theorems.Thm_Formalism_L2_Th1_D_B4_constantCoeff_defectOne
import Theorems.Thm_Formalism_L2_Th1_D_B4_constantCoeff_defectTwo
import Theorems.Thm_Formalism_L2_Th1_D_B4_iterate_of_pow
import Theorems.Thm_Formalism_L2_Th1_D_B4_exp_of_simeq
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_Transfer_cc_letterLog
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_Transfer_constantCoeff_defectOne
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_Transfer_constantCoeff_defectTwo
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_Top_lamModule


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.D
open Formalism.DworkPowerSeriesWeights (Integral mvExp torus BHyp NoLowBidegree letterLog de1 de2 s0 s1 s2 s1' s2' V2 degE)
open Formalism.InvariantFactorPaths.G7 (Simeq DivAB UnrOK IsLawOfLog)
open MvPowerSeries (subst HasSubst constantCoeff)
open B4
namespace Formalism.L2.Th1.D
theorem _root_.solution (h4 : TorusSumCoboundaryCondition) (hT : TorusTil) (hTe : TeichSigma) (h2 : MeanTorusInvariant) (h3 : MeanNoLowBidegreeTerms) :
    MeanBiextensionHypothesesOfCocycle := by
  intro K _ _ _ l d _ σ hU hd hev F hF be0 hF1 ι _ om oms hO ζ hζ
  have hl : 2 ≤ l := hU.1.two_le
  have hld : 2 ≤ l ^ d := le_trans hl (Nat.le_self_pow (by omega) l)
  have hN0 : l ^ d - 1 ≠ 0 := by omega
  have hζ1 : ζ ^ (l ^ d - 1) = 1 := hζ.pow_eq_one
  have hu1 : ∀ k : ℕ, (ζ ^ k) ^ (l ^ d - 1) = 1 := fun k => by
    rw [← pow_mul, mul_comm, pow_mul, hζ1, one_pow]
  have huσ : ∀ k : ℕ, σ (ζ ^ k) = (ζ ^ k) ^ l := fun k =>
    hTe K l d σ hU (by omega) (ζ ^ k) (hu1 k)
  have hun : ∀ k : ℕ, ‖ζ ^ k‖ = 1 := fun k =>
    (isOfFinOrder_iff_pow_eq_one.2 ⟨l ^ d - 1, Nat.pos_of_ne_zero hN0, hu1 k⟩).norm_eq_one
  have hu0 : ∀ k : ℕ, ζ ^ k ≠ 0 := fun k h => by
    have := hun k
    rw [h, norm_zero] at this
    exact zero_ne_one this
  have hud : ∀ k : ℕ, σ^[d] (ζ ^ k) = ζ ^ k := fun k => by
    rw [iterate_of_pow (huσ k) d]
    have : l ^ d = (l ^ d - 1) + 1 := by omega
    rw [this, pow_succ, hu1 k, one_mul]
  have hOk : ∀ k : ℕ, OwOK d σ (fun r => (ζ ^ k)⁻¹ * om r) (fun r => ζ ^ k * oms r) := by
    intro k
    refine ⟨fun r => ⟨?_, ?_⟩, fun r => ⟨?_, ?_⟩⟩
    · rw [norm_mul, norm_inv, hun k, inv_one, one_mul]
      exact (hO.1 r).1
    · rw [norm_mul, hun k, one_mul]
      exact (hO.1 r).2
    · have e := hud k
      have e' := (hO.2 r).1
      rw [← RingHom.coe_pow] at e e' ⊢
      rw [map_mul, map_inv₀, e, e']
    · have e := hud k
      have e' := (hO.2 r).2
      rw [← RingHom.coe_pow] at e e' ⊢
      rw [map_mul, e, e']
  have hmean : beMean (d := d) l σ be0 om oms ζ = MvPowerSeries.C (((l ^ d - 1 : ℕ) : K)⁻¹) *
      ∑ k ∈ Finset.range (l ^ d - 1),
        beTil l σ be0 (fun r => (ζ ^ k)⁻¹ * om r) (fun r => ζ ^ k * oms r) := by
    unfold beMean
    congr 1
    exact Finset.sum_congr rfl fun k _ => hT K l d σ hl be0 ι om oms (ζ ^ k) (hu0 k) (huσ k)
  have hb3 : NoLowBidegree (beMean (d := d) l σ be0 om oms ζ) :=
    h3 K l d σ hl hd hev be0 hF1.1 ι om oms ζ hζ
  have hcc : constantCoeff (beMean (d := d) l σ be0 om oms ζ) = 0 := by
    by_contra h
    have := (hb3 0 (by rwa [MvPowerSeries.coeff_zero_eq_constantCoeff_apply])).1
    simp [degE] at this
  have hc : ∀ x : V2 d, constantCoeff (letterLog (K := K) l x) = 0 :=
    Formalism.DworkPowerSeriesWeights.Transfer.cc_letterLog l
  have hLL : HasSubst (letterLog (K := K) (d := d) l) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero hc
  have hndvd : ¬ l ∣ l ^ d - 1 := by
    intro h
    have h' : l ∣ l ^ d := dvd_pow_self l (by omega)
    have : l ∣ 1 := by
      have := (Nat.dvd_sub h' h)
      rwa [Nat.sub_sub_self (by omega)] at this
    have := Nat.le_of_dvd one_pos this
    omega
  have hlam := Formalism.InvariantFactorPaths.G7.Top.lamModule K (V2 d) l σ hU.1 hU.2.2.1 hU.2.2.2.2
  refine ⟨fun n => Subfield.mem_top _, h2 K l d σ be0 ι om oms ζ hζ1, hb3, ?_, ?_⟩
  · refine exp_of_simeq l (constantCoeff_defectOne hcc) ?_
    rw [hmean, first_difference_C_mul_sum, subst_C_mul_sum hLL]
    exact hlam _ _ hndvd (simeq_sum_zero _ _ fun k _ =>
      (h4 K l d σ hU hd hev F hF be0 hF1 ι _ _ (hOk k)).1)
  · refine exp_of_simeq l (constantCoeff_defectTwo hcc) ?_
    rw [hmean, second_difference_C_mul_sum, subst_C_mul_sum hLL]
    exact hlam _ _ hndvd (simeq_sum_zero _ _ fun k _ =>
      (h4 K l d σ hU hd hev F hF be0 hF1 ι _ _ (hOk k)).2)
end Formalism.L2.Th1.D
