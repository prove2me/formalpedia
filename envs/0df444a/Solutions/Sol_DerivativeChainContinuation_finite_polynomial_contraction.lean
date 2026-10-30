-- Prove2me | solution 1 for DerivativeChainContinuation.finite_polynomial_contraction
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-27T03:45:21.280989+00:00
-- url     : https://prove2.me/submissions/998c0846-22f4-4f6e-93c8-375438ecf489

import Mathlib
import Definitions.Def_DerivativeChainContinuation_FinitePolynomialContraction
import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_DerivativeChainPrivate_bounded_holomorphic_contraction
open DerivativeChainPrivate Polynomial MeasureTheory Filter Set Topology Metric Function ComplexConjugate
open scoped BigOperators ComplexOrder Topology
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
set_option maxRecDepth 100000


set_option autoImplicit false
namespace DerivativeChainContinuation
open scoped BigOperators

theorem norm_power_difference_bound (k : ℕ) (v w : ℂ) (M : ℝ)
    (hM : 0 ≤ M) (hv : ‖v‖ ≤ M) (hw : ‖w‖ ≤ M) :
    ‖v^k-w^k‖ ≤ (k:ℝ)*M^(k-1)*‖v-w‖ := by
  induction k with
  | zero => simp
  | succ k ih =>
    have he : v^(k+1)-w^(k+1)=v*(v^k-w^k)+(v-w)*w^k := by ring
    rw [he]
    calc
      _ ≤ ‖v‖*‖v^k-w^k‖+‖v-w‖*‖w‖^k := by
        simpa only [norm_mul,norm_pow] using norm_add_le (v*(v^k-w^k)) ((v-w)*w^k)
      _ ≤ M*((k:ℝ)*M^(k-1)*‖v-w‖)+‖v-w‖*M^k := by
        exact add_le_add (mul_le_mul hv ih (norm_nonneg _) hM)
          (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hw k) (norm_nonneg _))
      _ = _ := by
        cases k with
        | zero => simp
        | succ k => simp only [Nat.succ_sub_one,Nat.cast_add,Nat.cast_one,pow_succ]; ring




end DerivativeChainContinuation

open DerivativeChainContinuation in
theorem solution (d : ℕ) (c : Fin (d+1) → ℂ → ℂ)
    (B : Fin (d+1) → ℝ) (R M : ℝ) (hR : 0 < R) (hM : 0 ≤ M)
    (hB : ∀ j,0 ≤ B j) (hc : ∀ j,Differentiable ℂ (c j))
    (hbound : ∀ t : ℂ,‖t‖ ≤ R → ∀ j,‖c j t‖ ≤ B j)
    (hmap : (∑ j,B j*M^j.val) ≤ M)
    (hcontract : (∑ j,B j*(j.val:ℝ)*M^(j.val-1)) ≤ 1/2)
    (hreal : ∀ j,∀ x : ℝ,(c j (x:ℂ)).im=0) :
    ∃ Y : ℂ → ℂ,
      (∀ t : ℂ,‖t‖ ≤ R → ‖Y t‖ ≤ M ∧ polynomialContractionMap d c t (Y t)=Y t) ∧
      DifferentiableOn ℂ Y (Metric.ball 0 R) ∧
      ∀ x : ℝ,|x| ≤ R → (Y (x:ℂ)).im=0 := by
  apply DerivativeChainPrivate.bounded_holomorphic_contraction (polynomialContractionMap d c) R M hR hM
  · unfold polynomialContractionMap
    apply Differentiable.fun_sum
    intro j _
    exact ((hc j).comp differentiable_fst).mul (differentiable_snd.pow j.val)
  · intro t ht y hy
    calc
      _ ≤ ∑ j,‖c j t‖*‖y‖^j.val := by
        simpa only [polynomialContractionMap,norm_mul,norm_pow] using norm_sum_le Finset.univ (fun j => c j t*y^j.val)
      _ ≤ ∑ j,B j*M^j.val := Finset.sum_le_sum fun j _ =>
        mul_le_mul (hbound t ht j) (pow_le_pow_left₀ (norm_nonneg _) hy j.val)
          (pow_nonneg (norm_nonneg _) _) (hB j)
      _ ≤ M := hmap
  · intro t ht v w hv hw
    unfold polynomialContractionMap
    rw [← Finset.sum_sub_distrib]
    calc
      _ ≤ ∑ j,‖c j t*(v^j.val-w^j.val)‖ := by
        simpa only [mul_sub] using norm_sum_le Finset.univ (fun j => c j t*v^j.val-c j t*w^j.val)
      _ ≤ ∑ j,B j*((j.val:ℝ)*M^(j.val-1)*‖v-w‖) := by
        apply Finset.sum_le_sum
        intro j _
        rw [norm_mul]
        exact mul_le_mul (hbound t ht j) (norm_power_difference_bound j.val v w M hM hv hw)
          (norm_nonneg _) (hB j)
      _ = (∑ j,B j*(j.val:ℝ)*M^(j.val-1))*‖v-w‖ := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ ≤ (1/2)*‖v-w‖ := mul_le_mul_of_nonneg_right hcontract (norm_nonneg _)
  · intro x y
    unfold polynomialContractionMap
    simp only [Complex.im_sum,Complex.mul_im,← Complex.ofReal_pow,Complex.ofReal_im,
      hreal,mul_zero,zero_mul,add_zero,Finset.sum_const_zero]
