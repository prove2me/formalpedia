-- Prove2me | solution 1 for AvramDividend.Classical.avram_a37_continuous_on_every_finite_horizon_implies_globally_continuous_20261114
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T09:25:38.231266+00:00
-- url     : https://prove2.me/submissions/6b2a472a-f0fb-4d48-9a1e-df9263eba7a0

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set Filter Topology
open scoped NNReal ENNReal
noncomputable section

theorem solution
    (f : ℝ≥0 → ℝ)
    (h : ∀ T : ℝ≥0, ContinuousOn f (Iic T)) :
    Continuous f := by
  rw [continuous_iff_continuousAt]
  intro t
  have ht : t < t + 1 :=
    lt_add_of_pos_right t (by norm_num : (0 : ℝ≥0) < 1)
  have hloc : ContinuousWithinAt f (Iic (t + 1)) t :=
    h (t + 1) t (Set.mem_Iic.mpr (le_of_lt ht))
  have hMem : Iic (t + 1) ∈ 𝓝 t :=
    mem_of_superset (Iio_mem_nhds ht) (fun u hu =>
      Set.mem_Iic.mpr (le_of_lt (Set.mem_Iio.mp hu)))
  exact hloc.continuousAt hMem
