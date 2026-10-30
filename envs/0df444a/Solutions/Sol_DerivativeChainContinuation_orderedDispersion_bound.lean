-- Prove2me | solution 1 for DerivativeChainContinuation.orderedDispersion_bound
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T17:06:54.742812+00:00
-- url     : https://prove2.me/submissions/2215b128-9ade-4745-9105-0a16f9f8b1dd

import Mathlib
import Definitions.Def_DerivativeChainContinuation_FiniteTransport
import Definitions.Def_DerivativeChainContinuation_RankDispersion
import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_DerivativeChainContinuation_rankWeight_square_sum
open DerivativeChainPrivate
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Polynomial
open scoped BigOperators


set_option autoImplicit false
namespace DerivativeChainContinuation
open scoped BigOperators







theorem orderedDispersion_square_bound {m : ℕ} (a : Fin m → ℝ) :
    (orderedDispersion a)^2 ≤ ((m : ℝ)*((m : ℝ)^2-1)/3)*(∑ i,(a i)^2) := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (rankWeight m) a
  rw [rankWeight_square_sum] at h
  exact h




end DerivativeChainContinuation

open DerivativeChainContinuation in
theorem solution (m : ℕ) (a : Fin (m+1) → ℝ)
    (K : ℝ) (hK : 0 ≤ K)
    (hs : ∑ i,(a i)^2 = 3*(m : ℝ)*(m+1)*K^2) :
    orderedDispersion a ≤ (m : ℝ)*(m+1)*Real.sqrt (m+2)*K := by
  have h := orderedDispersion_square_bound a
  rw [hs] at h
  have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ m+2 by positivity)
  have hn : (0 : ℝ) ≤ (m : ℝ)*(m+1)*Real.sqrt (m+2)*K := by positivity
  have he : (((m : ℝ)+1)*(((m : ℝ)+1)^2-1)/3)*(3*(m : ℝ)*(m+1)*K^2) =
      ((m : ℝ)*(m+1)*Real.sqrt (m+2)*K)^2 := by
    simp only [mul_pow]
    rw [hsq]
    ring
  push_cast at h
  rw [he] at h
  nlinarith
