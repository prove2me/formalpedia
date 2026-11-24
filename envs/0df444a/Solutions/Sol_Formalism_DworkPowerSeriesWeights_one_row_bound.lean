-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.one_row_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:47:17.449833+00:00
-- url     : https://prove2.me/submissions/ecfa1912-1ee3-44d5-b28c-2cd001d7027f

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Formalism_GaussJetBounds_StatementN
import Definitions.Def_Formalism_GaussJetBounds_MonoShapeTop
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_NormDetLeOneOfEntries
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ThmAOp
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_OneRow
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_minorProd_map
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_minorProd_mem_opInt
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_monoShapeLow
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_norm_inv_entry_le_one
import Theorems.Thm_Formalism_FG_InjVAux_HasOrd_mono
import Theorems.Thm_Formalism_FG_InvIntVAux_Low_mono
import Theorems.Thm_Formalism_G_LogCR_Agree_mono
import Theorems.Thm_Formalism_LT_CoeffP_Bd_mono
import Theorems.Thm_P2M_UpperTheory_Reformulated_B_Qi22_homW_prod__0e07eaea3260
import Theorems.Thm_P2M_UpperTheory_Reformulated_B_Qk29_wtGe_prod__77285e911b46


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
universe u
open Formalism Formalism.DworkPowerSeriesWeights
open MvPolynomial
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution : OneRow.{u} := by
  intro K _ _ N0 N1 Cn f hf hdet x hx p hp I
  classical
  have hne : f.det ≠ 0 := by
    intro h
    rw [h, norm_zero] at hdet
    exact zero_ne_one hdet
  have hunit : IsUnit f.det := isUnit_iff_ne_zero.mpr hne
  let X0 : Matrix (Fin N0) (Fin N0) K := Matrix.of x
  let γ : Matrix (Fin N0) (Fin N0) K := X0 * f⁻¹
  have hγint : ∀ i k, ‖γ i k‖ ≤ 1 := by
    intro i k
    show ‖(X0 * f⁻¹) i k‖ ≤ 1
    rw [Matrix.mul_apply]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun a _ => ?_
    rw [norm_mul]
    exact mul_le_one₀ (hx i a) (norm_nonneg _) (norm_inv_entry_le_one f hf hdet a k)
  have hγf : ∀ i a, (∑ k, γ i k * f k a) = x i a := by
    intro i a
    rw [← Matrix.mul_apply]
    show (X0 * f⁻¹ * f) i a = x i a
    rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hunit, Matrix.mul_one]
    rfl
  refine ⟨minorProd (oldRowLow (N1 := N1) (fun i k => γ i k)) p hp I, ?_, ?_, ?_⟩
  · refine minorProd_mem_opInt _ (fun i b => ?_) p hp I
    unfold oldRowLow
    refine Subring.sum_mem _ fun k _ => ?_
    intro κ
    rw [coeff_C_mul, coeff_X, norm_mul]
    refine mul_le_one₀ (hγint i k) (norm_nonneg _) ?_
    split_ifs <;> simp
  · rw [minorProd_map]
    congr 1
    funext i b
    unfold oldRowLow
    simp only [map_sum, map_mul, aeval_X, algHom_C, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← hγf i a, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, mul_assoc]
    rfl
  · intro mono hm a
    exact (monoShapeLow K N0 N1 N0 Cn (fun i k => γ i k) p hp I mono hm).2 a
end Formalism.DworkPowerSeriesWeights
