-- Prove2me | solution 1 for DerivativeChainContinuation.kernel_pair_bounds
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T19:28:52.630597+00:00
-- url     : https://prove2.me/submissions/cd63e953-9b64-4f4d-b68d-16f5dd83da2b

import Mathlib
import Definitions.Def_DerivativeChainContinuation_FiniteNormMean
import Definitions.Def_DerivativeChainPrivate_foundations
open DerivativeChainPrivate
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Polynomial Matrix
open scoped BigOperators
set_option maxHeartbeats 1000000


set_option autoImplicit false
namespace DerivativeChainContinuation
open scoped BigOperators

theorem finite_norm_mean_le {ι : Type*} [Fintype ι] (w : ι → ℝ) (z : ι → ℂ)
    (hw : ∀ i, 0 ≤ w i) :
    ‖∑ i, (w i : ℂ)*z i‖ ≤ ∑ i, w i*‖z i‖ := by
  calc
    _ ≤ ∑ i, ‖(w i : ℂ)*z i‖ := norm_sum_le _ _
    _ = _ := by simp [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw _)]

theorem finite_distance_mean_le {ι : Type*} [Fintype ι] (w : ι → ℝ) (z : ι → ℂ)
    (hw : ∀ i, 0 ≤ w i) (hs : ∑ i, w i=1) (b x : ℂ)
    (hm : ∑ i, (w i : ℂ)*z i=b) :
    ‖x-b‖ ≤ ∑ i, w i*‖x-z i‖ := by
  have he : (∑ i, (w i:ℂ)*(x-z i))=x-b := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, ← Complex.ofReal_sum, hs, hm]
    simp
  simpa only [he] using finite_norm_mean_le w (fun i => x-z i) hw








end DerivativeChainContinuation

open DerivativeChainContinuation in
theorem solution {ι κ : Type*} [Fintype κ]
    (K : ι → κ → ℝ) (x : ι → ℂ) (y : κ → ℂ)
    (hK : ∀ i a, 0 ≤ K i a) (hKs : ∀ i, ∑ a, K i a=1)
    (hKm : ∀ i, ∑ a, (K i a:ℂ)*y a=x i) (i j : ι) :
    ‖x i-x j‖ ≤ kernelPairDistance K y i j ∧
    kernelCost K x y i-‖x i-x j‖ ≤ kernelPairDistance K y i j := by
  have havg : (∑ a, K i a*‖y a-x j‖) ≤ kernelPairDistance K y i j := by
    apply Finset.sum_le_sum
    intro a _
    have hh := mul_le_mul_of_nonneg_left
      (finite_distance_mean_le (K j) y (hK j) (hKs j) (x j) (y a) (hKm j)) (hK i a)
    simpa only [Finset.mul_sum, mul_assoc] using hh
  constructor
  · have hh := finite_distance_mean_le (K i) y (hK i) (hKs i) (x i) (x j) (hKm i)
    simp only [norm_sub_rev (x j)] at hh
    exact hh.trans havg
  · have hh : kernelCost K x y i ≤ (∑ a, K i a*‖y a-x j‖)+‖x i-x j‖ := by
      calc
        _ ≤ ∑ a, K i a*(‖y a-x j‖+‖x i-x j‖) := by
          apply Finset.sum_le_sum
          intro a _
          apply mul_le_mul_of_nonneg_left _ (hK i a)
          have ht := norm_add_le (y a-x j) (x j-x i)
          rw [sub_add_sub_cancel] at ht
          simpa only [norm_sub_rev (x j) (x i)] using ht
        _ = _ := by simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hKs, one_mul]
    linarith
