-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_d_future_countable_borel_counts_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T12:17:45.938817+00:00
-- url     : https://prove2.me/submissions/f3bd889d-2712-46a1-9ee4-02496e06c134

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_d_future_intrinsic_general_time_mark_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- Every countable family of exact original Borel marked counts forms one
measurable ENNReal-valued observable on the original sample space. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (C : ℕ → Set (ℝ≥0 × ℝ))
    (hC : ∀ n, MeasurableSet (C n)) :
    Measurable (fun ω : Ω => fun n : ℕ =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (C n)) := by
  apply measurable_pi_iff.mpr
  intro n
  exact avram_p2_d_future_intrinsic_general_time_mark_measurable X (C n) (hC n)
