-- Prove2me | solution 1 for Formalism.DimensionVariation.coupled_norm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:14:48.52289+00:00
-- url     : https://prove2.me/submissions/d7ca153e-13a9-42a1-90e1-fbb2c2612a69

import Mathlib
import Definitions.Def_Formalism_ThetaSupremumBounds_StatementCB
import Definitions.Def_Formalism_ThetaSupremumBounds_DivIneqRecordTwoConst6
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_DescendedNorm
import Definitions.Def_Formalism_ThetaSupremumBounds_GaussianShiftBounds_PerEmbeddingCoupledBound

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
theorem _root_.solution : CoupledNorm := by
  intro AA Rep Y Cl2 Cl _ _ _ _ A B C _ _ _ _ _ _ γ0 γ1 γ2 ε1 T1 ε2 T2 t1 t2 a φ hγ0 hγ1 hγ2 hε1 hε2
    hT1 hT2 ht1 ht2
  have hs0 : 0 ≤ ∑ L, γ0 ⟨a, L⟩ * ‖φ L‖ :=
    Finset.sum_nonneg (fun L _ => mul_nonneg (hγ0 _).1.le (norm_nonneg _))
  have hS0 : 0 ≤ ∑ L, γ0 ⟨a, L⟩ * ‖φ L‖ ^ 2 :=
    Finset.sum_nonneg (fun L _ => mul_nonneg (hγ0 _).1.le (sq_nonneg _))
  have hin : ∀ (y : Y) (x : Rep), ‖liftOp (fun L => γ0 ⟨a, L⟩) (fun L x' => ε1 ⟨a, L⟩ ⟨y, x'⟩)
      (fun L x' => T1 ⟨a, L⟩ ⟨y, x'⟩) φ x‖ ≤ Real.sqrt t1 * ∑ L, γ0 ⟨a, L⟩ * ‖φ L‖ := by
    intro y x
    simp only [liftOp]
    rw [Finset.mul_sum]
    refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum (fun L _ => ?_))
    rw [norm_smul, norm_mul, hε1, mul_one, Complex.norm_real, Real.norm_of_nonneg (hγ0 _).1.le]
    calc γ0 ⟨a, L⟩ * ‖T1 ⟨a, L⟩ ⟨y, x⟩ (φ L)‖ ≤ γ0 ⟨a, L⟩ * (Real.sqrt t1 * ‖φ L‖) := by
          refine mul_le_mul_of_nonneg_left ?_ (hγ0 _).1.le
          refine le_trans (ContinuousLinearMap.le_opNorm _ _)
            (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
          exact le_of_eq_of_le (abs_of_nonneg (norm_nonneg _)).symm (Real.abs_le_sqrt (hT1 _ _))
      _ = Real.sqrt t1 * (γ0 ⟨a, L⟩ * ‖φ L‖) := by ring
  have hco : ∀ g', ‖coupledOp γ0 γ1 ε1 T1 ε2 T2 a φ g'‖ ≤
      (Fintype.card Rep : ℝ) * ((Fintype.card Y : ℝ) *
        (Real.sqrt t2 * (Real.sqrt t1 * ∑ L, γ0 ⟨a, L⟩ * ‖φ L‖))) := by
    intro g'
    simp only [coupledOp]
    calc _ ≤ ∑ _x : Rep, ∑ _y : Y, Real.sqrt t2 * (Real.sqrt t1 * ∑ L, γ0 ⟨a, L⟩ * ‖φ L‖) := by
          refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum (fun x _ => ?_))
          rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (hγ1 x).1.le]
          refine le_trans (mul_le_of_le_one_left (norm_nonneg _) (hγ1 x).2) ?_
          refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum (fun y _ => ?_))
          rw [norm_smul, hε2, one_mul]
          refine le_trans (ContinuousLinearMap.le_opNorm _ _) ?_
          exact mul_le_mul
            (le_of_eq_of_le (abs_of_nonneg (norm_nonneg _)).symm (Real.abs_le_sqrt (hT2 _ _)))
            (hin y x) (norm_nonneg _) (Real.sqrt_nonneg _)
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hsγ : ∑ L, γ0 ⟨a, L⟩ ≤ (Fintype.card (Cl a) : ℝ) := by
    calc ∑ L, γ0 ⟨a, L⟩ ≤ ∑ _L : Cl a, (1 : ℝ) := Finset.sum_le_sum (fun L _ => (hγ0 _).2)
      _ = _ := by simp
  have hcs : (∑ L, γ0 ⟨a, L⟩ * ‖φ L‖) ^ 2 ≤
      (Fintype.card (Cl a) : ℝ) * ∑ L, γ0 ⟨a, L⟩ * ‖φ L‖ ^ 2 :=
    le_trans (Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul _ (fun L _ => (hγ0 _).1.le)
        (fun L _ => mul_nonneg (hγ0 _).1.le (sq_nonneg _)) (fun L _ => by ring))
      (mul_le_mul_of_nonneg_right hsγ hS0)
  have key : ∀ g', ‖coupledOp γ0 γ1 ε1 T1 ε2 T2 a φ g'‖ ^ 2 ≤
      (Fintype.card Rep : ℝ) ^ 2 * (Fintype.card Y : ℝ) ^ 2 * t2 * t1 *
        ((Fintype.card (Cl a) : ℝ) * ∑ L, γ0 ⟨a, L⟩ * ‖φ L‖ ^ 2) := by
    intro g'
    have h1 := hco g'
    calc ‖coupledOp γ0 γ1 ε1 T1 ε2 T2 a φ g'‖ ^ 2
        ≤ ((Fintype.card Rep : ℝ) * ((Fintype.card Y : ℝ) *
            (Real.sqrt t2 * (Real.sqrt t1 * ∑ L, γ0 ⟨a, L⟩ * ‖φ L‖)))) ^ 2 :=
          sq_le_sq' (by linarith [norm_nonneg (coupledOp γ0 γ1 ε1 T1 ε2 T2 a φ g')]) h1
      _ = (Fintype.card Rep : ℝ) ^ 2 * (Fintype.card Y : ℝ) ^ 2 * t2 * t1 *
            (∑ L, γ0 ⟨a, L⟩ * ‖φ L‖) ^ 2 := by
          rw [mul_pow, mul_pow, mul_pow, mul_pow, Real.sq_sqrt ht2, Real.sq_sqrt ht1]
          ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hcs
          (mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) ht2) ht1)
  calc (∑ g', γ2 g' * ‖coupledOp γ0 γ1 ε1 T1 ε2 T2 a φ g'‖ ^ 2)
      ≤ ∑ _g' : Cl2, (Fintype.card Rep : ℝ) ^ 2 * (Fintype.card Y : ℝ) ^ 2 * t2 * t1 *
        ((Fintype.card (Cl a) : ℝ) * ∑ L, γ0 ⟨a, L⟩ * ‖φ L‖ ^ 2) :=
        Finset.sum_le_sum (fun g' _ =>
          le_trans (mul_le_of_le_one_left (sq_nonneg _) (hγ2 g').2) (key g'))
    _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        ring
end Formalism.DimensionVariation
