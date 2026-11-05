-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_b_bvjump_original_stopping_clock_measurable_from_filtration
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T07:53:46.216319+00:00
-- url     : https://prove2.me/submissions/6b2a3add-ba1a-416e-9a87-b3d2e347da41

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal ENNReal

/-- The bounded physical stopping-clock's finite NNReal value is measurable
from the original right-continuous filtration stopping-time condition. -/
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0))) :
    Measurable τ := by
  have hm : Measurable (fun ω => (τ ω : WithTop ℝ≥0)) :=
    hτ.measurable'
  have h := hm.untopD (0 : ℝ≥0)
  simpa only [WithTop.untopD_coe] using h
