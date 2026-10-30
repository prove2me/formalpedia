-- Prove2me | solution 1 for DerivativeChainContinuation.actual_tower_weighted_determinant_bound
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T19:01:02.349411+00:00
-- url     : https://prove2.me/submissions/25eaccee-3419-4aa6-a409-83e1182c3cbe

import Mathlib
import Definitions.Def_DerivativeChainContinuation_DeficitInequalities
import Definitions.Def_DerivativeChainContinuation_PolynomialMoments
import Definitions.Def_DerivativeChainContinuation_RootCovariance
import Definitions.Def_DerivativeChainContinuation_RowCovariance
import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_DerivativeChainContinuation_actual_tower_transverse_budget
import Theorems.Thm_DerivativeChainContinuation_deficit_determinant_inequality
open DerivativeChainPrivate
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Polynomial Matrix
open scoped BigOperators
set_option maxHeartbeats 1000000


open DerivativeChainContinuation in
theorem solution (P : ℕ → Polynomial ℂ) (n : ℕ)
    (hmonic : ∀ k ≤ n, (P (k+2)).Monic)
    (hdegree : ∀ k ≤ n, (P (k+2)).natDegree = k+2)
    (hcenter : ∀ k ≤ n, (P (k+2)).roots.sum = 0)
    (hstep : ∀ k < n, monicDerivative (P (k+3)) = P (k+2)) :
    (∑ k ∈ Finset.range n,
      (rootCovariance (P (k+3))).det/
        ((rootRadius (P (k+3)))^2*(k+2 : ℕ)*(k+1 : ℕ))) ≤
      4*transverseVariance (P (n+2))/(n+1 : ℕ) := by
  have ht := actual_tower_transverse_budget P n hmonic hdegree hcenter hstep
  have hs : (∑ k ∈ Finset.range n,
      (rootCovariance (P (k+3))).det/
        ((rootRadius (P (k+3)))^2*(k+2 : ℕ)*(k+1 : ℕ))) ≤
      2*∑ k ∈ Finset.range n,
        schoenbergDeficit (P (k+3))/((k+2 : ℕ)*(k+1 : ℕ) : ℝ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro k hk
    have hk' : k < n := Finset.mem_range.mp hk
    have hd : 2 ≤ (P (k+3)).natDegree := by
      rw [hdegree (k+1) (by omega)]; omega
    have h := deficit_determinant_inequality (P (k+3))
      (hmonic (k+1) (by omega)) hd (hcenter (k+1) (by omega))
    have h' := div_le_div_of_nonneg_right h (by positivity :
      0 ≤ ((k+2 : ℕ)*(k+1 : ℕ) : ℝ))
    convert mul_le_mul_of_nonneg_left h' (by norm_num : (0 : ℝ) ≤ 2) using 1 <;> ring
  rw [ht] at hs
  convert hs using 1 <;> dsimp [transverseVariance] <;> ring
