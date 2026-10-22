-- Prove2me | solution 1 for AvramDividend.Classical.gaussian_double_tail_conditional_atom_lipschitz
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T18:29:59.77763+00:00
-- url     : https://prove2.me/submissions/a4c87962-9373-463f-95d1-a8002350bdad

import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Order.Interval.Set.Basic
import Theorems.Thm_AvramDividend_Classical_gaussian_double_tail_atom_lipschitz_time

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- The strict-order conditional kernel is locally time-Lipschitz on (0,∞). -/
theorem solution
    (φ z s t : ℝ) (hs : 0 < s) (ht : 0 < t) :
    |(if 0 < t ∧ t < z then (z - t) * Real.exp (-φ * z) else 0) -
      (if 0 < s ∧ s < z then (z - s) * Real.exp (-φ * z) else 0)| ≤
      |t - s| * Real.exp (-φ * z) := by
  have hrepr (u : ℝ) (hu : 0 < u) :
      (if 0 < u ∧ u < z then (z - u) * Real.exp (-φ * z) else 0) =
        max (z - u) 0 * Real.exp (-φ * z) := by
    by_cases huz : u < z
    · have hnonneg : 0 ≤ z - u := sub_nonneg.mpr huz.le
      simp [hu, huz, max_eq_left hnonneg]
    · have hnonpos : z - u ≤ 0 := sub_nonpos.mpr (le_of_not_gt huz)
      simp [hu, huz, max_eq_right hnonpos]
  rw [hrepr t ht, hrepr s hs]
  exact AvramDividend.Classical.gaussian_double_tail_atom_lipschitz_time
    φ z s t
