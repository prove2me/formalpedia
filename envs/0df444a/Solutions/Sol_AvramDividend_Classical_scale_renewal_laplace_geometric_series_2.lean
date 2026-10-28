-- Prove2me | solution 2 for AvramDividend.Classical.scale_renewal_laplace_geometric_series
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T21:28:03.822577+00:00
-- url     : https://prove2.me/submissions/3c8706bc-f79b-4fbe-b392-2bb4684a8c40

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Ring
open AvramDividend.Classical

theorem solution
    (q ψ : ℝ) (hq : 0 ≤ q) (hψ : 0 < ψ) (hqψ : q < ψ) :
    (∑' n : ℕ, q ^ n * (ψ⁻¹) ^ (n + 1)) = (ψ - q)⁻¹ := by
  have hr0 : 0 ≤ q / ψ := div_nonneg hq hψ.le
  have hr1 : q / ψ < 1 := (div_lt_one hψ).2 hqψ
  have h : ∀ n : ℕ, q ^ n * (ψ⁻¹) ^ (n + 1) = ψ⁻¹ * (q / ψ) ^ n := by
    intro n; rw [pow_succ, div_eq_mul_inv, mul_pow]; ring
  simp_rw [h]
  rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1]
  have : ψ - q ≠ 0 := by linarith
  field_simp
