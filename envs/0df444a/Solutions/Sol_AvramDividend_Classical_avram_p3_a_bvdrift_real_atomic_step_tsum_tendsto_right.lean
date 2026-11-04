-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_a_bvdrift_real_atomic_step_tsum_tendsto_right
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T15:58:46.282219+00:00
-- url     : https://prove2.me/submissions/7277683b-c578-4893-8dd9-47e84343610f

import Mathlib
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Topology.Order.LeftRightLim

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter Set Topology
open scoped NNReal BigOperators

/-- An absolutely summable real atomic cumulative series converges from
the right to the sum including its time-t atom, including at time zero. -/
theorem solution
    (f : ℝ≥0 → ℝ) (hSum : Summable (fun u : ℝ≥0 => |f u|))
    (t : ℝ≥0) :
    Filter.Tendsto
      (fun s : ℝ≥0 => ∑' u : ℝ≥0,
        if 0 < u ∧ u ≤ s then f u else 0)
      (𝓝[>] t)
      (nhds (∑' u : ℝ≥0, if 0 < u ∧ u ≤ t then f u else 0)) := by
  classical
  apply tendsto_tsum_of_dominated_convergence hSum
  · intro u
    by_cases hu : 0 < u
    · by_cases hut : u ≤ t
      · have hev : ∀ᶠ s : ℝ≥0 in 𝓝[>] t, t < s :=
          self_mem_nhdsWithin
        have heq :
            (fun s : ℝ≥0 => if 0 < u ∧ u ≤ s then f u else 0) =ᶠ[𝓝[>] t]
              (fun _ : ℝ≥0 => if 0 < u ∧ u ≤ t then f u else 0) := by
          filter_upwards [hev] with s hts
          have hus : u ≤ s := hut.trans (le_of_lt hts)
          simp [hu, hut, hus]
        exact tendsto_const_nhds.congr' heq.symm
      · have htu : t < u := lt_of_not_ge hut
        have hev : ∀ᶠ s : ℝ≥0 in 𝓝[>] t, s < u := by
          have hnhds : ∀ᶠ s : ℝ≥0 in nhds t, s < u :=
            isOpen_Iio.mem_nhds htu
          exact hnhds.filter_mono nhdsWithin_le_nhds
        have heq :
            (fun s : ℝ≥0 => if 0 < u ∧ u ≤ s then f u else 0) =ᶠ[𝓝[>] t]
              (fun _ : ℝ≥0 => if 0 < u ∧ u ≤ t then f u else 0) := by
          filter_upwards [hev] with s hsu
          have hnot : ¬ u ≤ s := not_le.mpr hsu
          simp [hu, hut, hnot]
        exact tendsto_const_nhds.congr' heq.symm
    · simpa [hu] using
        (tendsto_const_nhds :
          Filter.Tendsto (fun _ : ℝ≥0 => (0 : ℝ)) (𝓝[>] t) (nhds 0))
  · apply Filter.Eventually.of_forall
    intro s u
    by_cases hu : 0 < u ∧ u ≤ s
    · simp [hu, Real.norm_eq_abs]
    · simp [hu, abs_nonneg]
