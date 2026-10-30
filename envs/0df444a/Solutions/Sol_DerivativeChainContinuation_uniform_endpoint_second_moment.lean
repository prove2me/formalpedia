-- Prove2me | solution 1 for DerivativeChainContinuation.uniform_endpoint_second_moment
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T17:29:31.835432+00:00
-- url     : https://prove2.me/submissions/e5865b92-2c66-4e19-a4bd-f8dbdac6a989

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations
open DerivativeChainPrivate
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Polynomial
open scoped BigOperators


set_option autoImplicit false
namespace DerivativeChainContinuation
open scoped BigOperators

theorem pairwise_square_sum (n : ℕ) (f : Fin n → ℝ) :
    (∑ i, ∑ j, (f i-f j)^2) =
      2*((n : ℝ)*(∑ i, (f i)^2)-(∑ i, f i)^2) := by
  simp_rw [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp [← Finset.mul_sum, ← Finset.sum_mul]
  ring

theorem endpoint_variance_lipschitz (n : ℕ) (x f : Fin n → ℝ)
    (h : ∀ i j, |f i-f j| ≤ |x i-x j|) :
    (n : ℝ)*(∑ i, (f i)^2)-(∑ i, f i)^2 ≤
      (n : ℝ)*(∑ i, (x i)^2)-(∑ i, x i)^2 := by
  have hs : (∑ i, ∑ j, (f i-f j)^2) ≤ ∑ i, ∑ j, (x i-x j)^2 := by
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j _
    exact sq_le_sq.mpr (h i j)
  rw [pairwise_square_sum, pairwise_square_sum] at hs
  linarith




end DerivativeChainContinuation

open DerivativeChainContinuation in
theorem solution (n : ℕ) (hn : 0 < n)
    (x f : Fin n → ℝ) (hcenter : ∑ i, x i = 0)
    (hcost : ∀ i, 0 ≤ f i)
    (hlip : ∀ i j, |f i-f j| ≤ |x i-x j|)
    (B : ℝ) (hB : 0 ≤ B)
    (hmean : (∑ i, f i)/(n : ℝ) ≤ B*Real.sqrt ((∑ i, (x i)^2)/(n : ℝ))) :
    (∑ i, (f i)^2)/(n : ℝ) ≤ (1+B^2)*((∑ i, (x i)^2)/(n : ℝ)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hx : 0 ≤ (∑ i, (x i)^2)/(n : ℝ) := by positivity
  have hf : 0 ≤ (∑ i, f i)/(n : ℝ) :=
    div_nonneg (Finset.sum_nonneg fun i _ => hcost i) hnR.le
  have hbroot : 0 ≤ B*Real.sqrt ((∑ i, (x i)^2)/(n : ℝ)) := by positivity
  have hm := (sq_le_sq₀ hf hbroot).mpr hmean
  rw [mul_pow, Real.sq_sqrt hx] at hm
  have hv := endpoint_variance_lipschitz n x f hlip
  rw [hcenter, zero_pow (by decide : 2 ≠ 0), sub_zero] at hv
  have hm' : (∑ i, f i)^2 ≤ B^2 * (∑ i, (x i)^2) * (n : ℝ) := by
    field_simp at hm
    nlinarith
  rw [← mul_div_assoc]
  apply (div_le_div_iff_of_pos_right hnR).mpr
  nlinarith
