-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_a_bvdrift_real_atomic_step_tsum_tendsto_left
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T15:10:42.189193+00:00
-- url     : https://prove2.me/submissions/85bdce23-ad26-4165-b25f-a8be6d4e4a87

import Mathlib
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Topology.Order.LeftRightLim

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter Set Topology
open scoped NNReal BigOperators

/-- An absolutely summable real atomic cumulative jump path converges
to its strict-past sum when observed from the left at positive time. -/
theorem solution
    (f : ℝ≥0 → ℝ) (hSum : Summable (fun u : ℝ≥0 => |f u|))
    (t : ℝ≥0) (ht : 0 < t) :
    Filter.Tendsto
      (fun s : ℝ≥0 =>
        ∑' u : ℝ≥0, if 0 < u ∧ u ≤ s then f u else 0)
      (𝓝[<] t)
      (nhds (∑' u : ℝ≥0, if 0 < u ∧ u < t then f u else 0)) := by
  classical
  apply tendsto_tsum_of_dominated_convergence hSum
  · intro u
    by_cases hu : 0 < u
    · by_cases hut : u < t
      · have hev : ∀ᶠ s : ℝ≥0 in 𝓝[<] t, u ≤ s := by
          have hnhds : ∀ᶠ s : ℝ≥0 in nhds t, u < s :=
            (isOpen_Ioi.mem_nhds hut)
          exact (hnhds.filter_mono nhdsWithin_le_nhds).mono
            (fun s hs => le_of_lt hs)
        have heq :
            (fun s : ℝ≥0 => if 0 < u ∧ u ≤ s then f u else 0) =ᶠ[𝓝[<] t]
              (fun _ : ℝ≥0 => if 0 < u ∧ u < t then f u else 0) := by
          filter_upwards [hev] with s hus
          simp [hu, hut, hus]
        exact tendsto_const_nhds.congr' heq.symm
      · have htu : t ≤ u := le_of_not_gt hut
        have hev : ∀ᶠ s : ℝ≥0 in 𝓝[<] t, s < t :=
          self_mem_nhdsWithin
        have heq :
            (fun s : ℝ≥0 => if 0 < u ∧ u ≤ s then f u else 0) =ᶠ[𝓝[<] t]
              (fun _ : ℝ≥0 => if 0 < u ∧ u < t then f u else 0) := by
          filter_upwards [hev] with s hst
          have hnot : ¬ u ≤ s := not_le.mpr (lt_of_lt_of_le hst htu)
          simp [hu, hut, hnot]
        exact tendsto_const_nhds.congr' heq.symm
    · simpa [hu] using
        (tendsto_const_nhds :
          Filter.Tendsto (fun _ : ℝ≥0 => (0 : ℝ)) (𝓝[<] t) (nhds 0))
  · apply Filter.Eventually.of_forall
    intro s u
    by_cases hu : 0 < u ∧ u ≤ s
    · simp [hu, Real.norm_eq_abs]
    · simp [hu, abs_nonneg]
