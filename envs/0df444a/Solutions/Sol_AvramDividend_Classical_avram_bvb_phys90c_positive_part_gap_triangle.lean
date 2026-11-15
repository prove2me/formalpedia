-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_phys90c_positive_part_gap_triangle
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T00:15:04.427533+00:00
-- url     : https://prove2.me/submissions/bedb86fd-92e8-42d5-9fed-2231a42ff82b

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter
open scoped Topology
theorem solution
    (f g h : ℕ → ℝ)
    (hfg : Tendsto (fun n => max (f n - g n) 0) atTop (𝓝 0))
    (hgh : Tendsto (fun n => max (g n - h n) 0) atTop (𝓝 0)) :
    Tendsto (fun n => max (f n - h n) 0) atTop (𝓝 0) := by
  have hnonneg (n : ℕ) : 0 ≤ max (f n - h n) 0 := le_max_right _ _
  have hupper (n : ℕ) :
      max (f n - h n) 0 ≤
        max (f n - g n) 0 + max (g n - h n) 0 := by
    apply max_le
    · have hfg' := le_max_left (f n - g n) (0 : ℝ)
      have hgh' := le_max_left (g n - h n) (0 : ℝ)
      linarith
    · exact add_nonneg (le_max_right _ _) (le_max_right _ _)
  have hadd : Tendsto
      (fun n => max (f n - g n) 0 + max (g n - h n) 0)
      atTop (𝓝 (0 : ℝ)) := by
    simpa using (Filter.Tendsto.add hfg hgh)
  exact squeeze_zero hnonneg hupper hadd
