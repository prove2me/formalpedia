-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_phys104_weighted_physical_grid_quadrature_can_miss_positive_occupation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T10:19:17.545315+00:00
-- url     : https://prove2.me/submissions/a72c3b40-e5a9-4101-876d-14fe674dfa73

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bvb_phys102_positive_occupation_can_escape_every_uniform_grid_sample

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set

/-- Even weighted physical-grid sums can vanish identically while
the underlying threshold-occupation set has positive volume. -/
theorem solution (u : ℕ → ℕ → ℝ) (Δ : ℕ → ℕ → ℝ) :
    ∃ f : ℝ → ℝ,
      (∀ n : ℕ,
        (∑ i ∈ Finset.range (n + 1), f (u n i) * Δ n i) = 0) ∧
      0 < (volume : Measure ℝ) {t : ℝ | f t = 1} := by
  obtain ⟨f, hgrid, _, hpos⟩ :=
    AvramDividend.Classical.avram_bvb_phys102_positive_occupation_can_escape_every_uniform_grid_sample u
  refine ⟨f, ?_, hpos⟩
  intro n
  apply Finset.sum_eq_zero
  intro i hi
  simp [hgrid n i]
