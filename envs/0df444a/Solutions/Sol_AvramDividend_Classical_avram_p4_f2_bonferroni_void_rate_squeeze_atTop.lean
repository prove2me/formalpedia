-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f2_bonferroni_void_rate_squeeze_atTop
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T01:00:45.254446+00:00
-- url     : https://prove2.me/submissions/c7ed117b-c39b-42b1-a9dd-1312c65f567d

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter Topology
noncomputable section

/-- An O(1/k) lower Bonferroni error forces the exact jump-rate limit. -/
theorem solution
    (r : ℝ) (p : ℕ → ℝ)
    (hBound : ∀ k : ℕ, 0 < k →
      r - (r ^ 2 / 2) * (k : ℝ)⁻¹ ≤ (k : ℝ) * p k ∧
      (k : ℝ) * p k ≤ r) :
    Filter.Tendsto (fun k : ℕ => (k : ℝ) * p k)
      Filter.atTop (nhds r) := by
  have hNat : Filter.Tendsto (fun k : ℕ => (k : ℝ))
      Filter.atTop Filter.atTop := tendsto_natCast_atTop_atTop
  have hInv : Filter.Tendsto (fun k : ℕ => (k : ℝ)⁻¹)
      Filter.atTop (nhds (0 : ℝ)) :=
    tendsto_inv_atTop_zero.comp hNat
  have hConst : Filter.Tendsto (fun _ : ℕ => r ^ 2 / 2)
      Filter.atTop (nhds (r ^ 2 / 2)) := tendsto_const_nhds
  have hLower : Filter.Tendsto
      (fun k : ℕ => r - (r ^ 2 / 2) * (k : ℝ)⁻¹)
      Filter.atTop (nhds r) := by
    have hProd := hConst.mul hInv
    have hSub := (tendsto_const_nhds : Filter.Tendsto
      (fun _ : ℕ => r) Filter.atTop (nhds r)).sub hProd
    simpa using hSub
  have hLowerLe : ∀ᶠ k : ℕ in Filter.atTop,
      r - (r ^ 2 / 2) * (k : ℝ)⁻¹ ≤ (k : ℝ) * p k :=
    (eventually_gt_atTop (0 : ℕ)).mono (fun k hk => (hBound k hk).1)
  have hUpperLe : ∀ᶠ k : ℕ in Filter.atTop,
      (k : ℝ) * p k ≤ r :=
    (eventually_gt_atTop (0 : ℕ)).mono (fun k hk => (hBound k hk).2)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    hLower tendsto_const_nhds hLowerLe hUpperLe
