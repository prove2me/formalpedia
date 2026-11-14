-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a154_original_gaussian_fullcell_raw_source_sum_cauchy_energy
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T12:26:17.902261+00:00
-- url     : https://prove2.me/submissions/a1a958c2-28b8-4e03-a889-78bf737dfdb9

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical
noncomputable section

/-- Raw source absolute increments on the original full physical Gaussian m-cell mesh obey finite Cauchy-Schwarz energy control. -/
theorem solution
    (m : ℕ) (R : ℕ → ℝ) :
    (∑ i ∈ Finset.range m, |R i|)^2 ≤
      (m : ℝ) * (∑ i ∈ Finset.range m, (R i)^2) := by
  simpa only [Finset.card_range, sq_abs] using
    (sq_sum_le_card_mul_sum_sq
      (s := Finset.range m) (f := fun i => |R i|))
