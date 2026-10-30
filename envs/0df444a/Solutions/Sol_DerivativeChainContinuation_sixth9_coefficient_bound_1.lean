-- Prove2me | solution 1 for DerivativeChainContinuation.sixth9_coefficient_bound_1
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-28T04:31:54.635935+00:00
-- url     : https://prove2.me/submissions/57c3f744-17c2-4b56-aab9-11e4f8a3595f

import Mathlib
import Definitions.Def_DerivativeChainContinuation_Sixth9C1Data
import Definitions.Def_DerivativeChainPrivate_foundations
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open Polynomial DerivativeChainPrivate MeasureTheory Set Filter
namespace DerivativeChainContinuation
end DerivativeChainContinuation
open DerivativeChainContinuation
open scoped Topology BigOperators



set_option autoImplicit false
namespace DerivativeChainPrivate
open scoped BigOperators















theorem norm_real_power_sum_le {n : ℕ} (c : Fin n → ℝ) (u : ℂ) (R : ℝ)
    (hR : 0 ≤ R) (hu : ‖u‖ ≤ R) :
    ‖∑ i : Fin n, (c i:ℂ)*u^i.val‖ ≤ ∑ i : Fin n, |c i| *R^i.val := by
  calc
    _ ≤ ∑ i : Fin n, ‖(c i:ℂ)*u^i.val‖ := norm_sum_le _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs]
      gcongr











end DerivativeChainPrivate

theorem solution (t : ℂ) (ht : ‖t‖ ≤ 2) : ‖sixth9C1 t‖ ≤ 1/100000 := by
  apply (DerivativeChainPrivate.norm_real_power_sum_le sixth9C1Coeffs t 2 (by norm_num) ht).trans
  norm_num (config := { maxSteps := 1000000 }) [sixth9C1Coeffs,Fin.sum_univ_succ]
