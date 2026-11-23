-- Prove2me | solution 1 for Formalism.DimensionVariation.sharp_norm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:31:44.273268+00:00
-- url     : https://prove2.me/submissions/a2497d4a-11c4-4596-9f10-9743c668f253

import Mathlib
import Definitions.Def_Formalism_ThetaSupremumBounds_StatementCB
import Definitions.Def_Formalism_ThetaSupremumBounds_DivIneqRecordTwoConst6
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_DescendedNorm
import Definitions.Def_Formalism_ThetaSupremumBounds_GaussianShiftBounds_PerEmbeddingCoupledBound
import Theorems.Thm_Formalism_DimensionVariation_CB_const_le
import Theorems.Thm_Formalism_DimensionVariation_CB_cbSq_nonneg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField
open scoped Real
open Formalism Formalism.DimensionVariation
open Formalism.LatticeIndexTer (ph)
open Formalism.DivisionValues (fnorm chainFun chainMat)
open CB
namespace Formalism.DimensionVariation
theorem _root_.solution : SharpNorm := by
  intro AA AA' _ _ Cl Cl' _ _ A B _ _ _ _ γ γ' ε T h h' tmax hγ hγ' hε hT ht hh hh'
  have hPQ : (Fintype.card (Σ a, Cl a) : ℝ) * (Fintype.card (Σ b, Cl' b) : ℝ) * tmax ≤
      cbSq (Fintype.card AA) (Fintype.card AA') h h' tmax :=
    const_le Cl Cl' h h' tmax ht hh hh'
  have hcb0 : 0 ≤ cbSq (Fintype.card AA) (Fintype.card AA') h h' tmax :=
    cbSq_nonneg Cl Cl' h h' tmax ht hh hh'
  have hsumγ : ∑ p, γ p ≤ (Fintype.card (Σ a, Cl a) : ℝ) := by
    calc ∑ p, γ p ≤ ∑ _p : (Σ a, Cl a), (1 : ℝ) := Finset.sum_le_sum (fun p _ => (hγ p).2)
      _ = (Fintype.card (Σ a, Cl a) : ℝ) := by simp
  have key : ∀ G : (Σ a, Cl a) → A, ∀ q, ‖liftOp γ ε T G q‖ ^ 2 ≤
      tmax * ((Fintype.card (Σ a, Cl a) : ℝ) * ∑ p, γ p * ‖G p‖ ^ 2) := by
    intro G q
    have h1 : ‖liftOp γ ε T G q‖ ≤ ∑ p, γ p * (Real.sqrt tmax * ‖G p‖) := by
      unfold liftOp
      refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum (fun p _ => ?_))
      rw [norm_smul, norm_mul, hε p q, mul_one, Complex.norm_real, Real.norm_of_nonneg (hγ p).1.le]
      refine mul_le_mul_of_nonneg_left ?_ (hγ p).1.le
      refine le_trans (ContinuousLinearMap.le_opNorm _ _) (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
      exact le_of_eq_of_le (abs_of_nonneg (norm_nonneg _)).symm (Real.abs_le_sqrt (hT p q))
    have h2 : (∑ p, γ p * (Real.sqrt tmax * ‖G p‖)) = Real.sqrt tmax * ∑ p, γ p * ‖G p‖ := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun p _ => by ring)
    have h3 : (∑ p, γ p * ‖G p‖) ^ 2 ≤ (∑ p, γ p) * ∑ p, γ p * ‖G p‖ ^ 2 :=
      Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul _ (fun p _ => (hγ p).1.le)
        (fun p _ => mul_nonneg (hγ p).1.le (sq_nonneg _)) (fun p _ => by ring)
    have hS : 0 ≤ ∑ p, γ p * ‖G p‖ ^ 2 :=
      Finset.sum_nonneg (fun p _ => mul_nonneg (hγ p).1.le (sq_nonneg _))
    rw [h2] at h1
    calc ‖liftOp γ ε T G q‖ ^ 2 ≤ (Real.sqrt tmax * ∑ p, γ p * ‖G p‖) ^ 2 :=
          sq_le_sq' (by linarith [norm_nonneg (liftOp γ ε T G q)]) h1
      _ = tmax * (∑ p, γ p * ‖G p‖) ^ 2 := by rw [mul_pow, Real.sq_sqrt ht]
      _ ≤ tmax * ((∑ p, γ p) * ∑ p, γ p * ‖G p‖ ^ 2) := mul_le_mul_of_nonneg_left h3 ht
      _ ≤ tmax * ((Fintype.card (Σ a, Cl a) : ℝ) * ∑ p, γ p * ‖G p‖ ^ 2) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hsumγ hS) ht
  have bound : ∀ G : (Σ a, Cl a) → A, (∑ q, γ' q * ‖liftOp γ ε T G q‖ ^ 2) ≤
      cbSq (Fintype.card AA) (Fintype.card AA') h h' tmax * ∑ p, γ p * ‖G p‖ ^ 2 := by
    intro G
    have hS : 0 ≤ ∑ p, γ p * ‖G p‖ ^ 2 :=
      Finset.sum_nonneg (fun p _ => mul_nonneg (hγ p).1.le (sq_nonneg _))
    calc (∑ q, γ' q * ‖liftOp γ ε T G q‖ ^ 2)
        ≤ ∑ _q : (Σ b, Cl' b), tmax * ((Fintype.card (Σ a, Cl a) : ℝ) * ∑ p, γ p * ‖G p‖ ^ 2) :=
          Finset.sum_le_sum (fun q _ =>
            le_trans (mul_le_of_le_one_left (sq_nonneg _) (hγ' q).2) (key G q))
      _ = (Fintype.card (Σ a, Cl a) : ℝ) * (Fintype.card (Σ b, Cl' b) : ℝ) * tmax *
            ∑ p, γ p * ‖G p‖ ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hPQ hS
  refine ⟨bound, ?_⟩
  unfold liftNormSq
  exact csInf_le ⟨0, fun X hX => hX.1⟩ ⟨hcb0, bound⟩
end Formalism.DimensionVariation
