-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_a_zero_rate_positive_horizon_to_closed_significant_jumps
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T21:06:37.057611+00:00
-- url     : https://prove2.me/submissions/96c7209d-26cf-4a0e-91d1-795de5de2687

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_original_full_grid_compact_test_jump_limit

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter Set Topology AvramDividend.Classical
open scoped NNReal

/-- A process with no jump at the time origin has the same significant
jump containment on the closed horizon as on the positive-time horizon. -/
theorem solution
    (Y : ℝ≥0 → ℝ) (T : ℝ≥0)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hzero : Y 0 = Function.leftLim Y 0)
    (F : Finset ℝ≥0)
    (hF : ∀ t ∈ Ioc (0 : ℝ≥0) T,
      ρ ≤ |Y t - Function.leftLim Y t| → t ∈ F) :
    ∀ t ∈ Icc (0 : ℝ≥0) T,
      ρ ≤ |Y t - Function.leftLim Y t| → t ∈ F := by
  intro t ht hlarge
  obtain ⟨ht0, htT⟩ := Set.mem_Icc.mp ht
  by_cases hpos : 0 < t
  · exact hF t (Set.mem_Ioc.mpr ⟨hpos, htT⟩) hlarge
  · have hz : t = 0 := le_antisymm (le_of_not_gt hpos) ht0
    subst t
    have hbad : ρ ≤ (0 : ℝ) := by
      simpa [hzero] using hlarge
    exact False.elim ((not_le_of_gt hρ) hbad)
