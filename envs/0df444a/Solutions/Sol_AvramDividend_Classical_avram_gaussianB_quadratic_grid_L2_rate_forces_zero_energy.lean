-- Prove2me | solution 1 for AvramDividend.Classical.avram_gaussianB_quadratic_grid_L2_rate_forces_zero_energy
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T00:40:41.488142+00:00
-- url     : https://prove2.me/submissions/6a7a6f37-2d39-4b3b-abbd-fae059a9f1a4

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Order.Basic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter
open scoped Topology
noncomputable section
/-- Quadratic-grid second-moment energy decays to zero at its O(1/m) rate. -/
theorem solution
    (K : ℝ) (hK : 0 ≤ K)
    (a : ℕ → ℝ)
    (hNonneg : ∀ m, 0 ≤ a m)
    (hRate : ∀ m, a m ≤ K / ((m + 1 : ℕ) : ℝ)) :
    Tendsto a atTop (𝓝 (0 : ℝ)) := by
  have hInv :
      Tendsto (fun m : ℕ => K * (1 / ((m + 1 : ℕ) : ℝ)))
        atTop (𝓝 (0 : ℝ)) := by
    simpa using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul K
  have hUpper :
      Tendsto (fun m : ℕ => K / ((m + 1 : ℕ) : ℝ))
        atTop (𝓝 (0 : ℝ)) := by
    simpa only [div_eq_mul_inv, one_mul] using hInv
  exact squeeze_zero hNonneg hRate hUpper
