-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva_capHJB39_original_continuity_away_from_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T22:45:34.130498+00:00
-- url     : https://prove2.me/submissions/ea033eaa-5caf-42a5-9352-057ebc564b79

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter
open scoped Topology
noncomputable section

/- Revalidation with current CLI checker. Original candidate w continuous on nonnegative reserves and zero on negatives is continuous away from zero. -/
theorem solution
    (w : ℝ → ℝ)
    (hwCont : ContinuousOn w (Ici (0 : ℝ)))
    (hwNeg : ∀ y : ℝ, y < 0 → w y = 0)
    (r : ℝ) (hr : r ≠ 0) :
    ContinuousAt w r := by
  rcases lt_or_gt_of_ne hr with hneg | hpos
  · have heq : (fun _ : ℝ => (0 : ℝ)) =ᶠ[𝓝 r] w := by
      filter_upwards [Iio_mem_nhds hneg] with y hy
      exact (hwNeg y hy).symm
    have h0 : Tendsto (fun _ : ℝ => (0 : ℝ))
        (𝓝 r) (𝓝 (w r)) := by
      simpa [hwNeg r hneg] using
        (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℝ))
          (𝓝 r) (𝓝 (0 : ℝ)))
    exact h0.congr' heq
  · have hmem : Ici (0 : ℝ) ∈ 𝓝 r :=
      Filter.mem_of_superset (Ioi_mem_nhds hpos) Ioi_subset_Ici_self
    exact hwCont.continuousAt hmem
