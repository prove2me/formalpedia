-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f3_original_postpayment_reserve_grid_telescope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T23:56:26.072204+00:00
-- url     : https://prove2.me/submissions/0a5ab1fd-7549-494b-b014-c76c3b6ad948

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_prepost_reserve_two_clock_increment
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- Telescope the original post-rightpayment reserve over the finite source grid. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (u : ℕ → ℝ≥0) (n : ℕ) (ω : Ω) :
    (∑ i ∈ Finset.range n,
      ((X.X (u (i + 1)) ω - X.X (u i) ω) -
        (rightLimit D (u (i + 1)) ω - rightLimit D (u i) ω))) =
    (riskProcess X x D (u n) ω -
      (rightLimit D (u n) ω - D (u n) ω)) -
    (riskProcess X x D (u 0) ω -
      (rightLimit D (u 0) ω - D (u 0) ω)) := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      have hcell :=
        (avram_p4_f3_original_prepost_reserve_two_clock_increment
          X x D (u n) (u (n + 1)) ω).2
      rw [← hcell]
      ring
