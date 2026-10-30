-- Prove2me | solution 1 for AvramDividend.Classical.avram_root29_03_up_first_iff_finite_stopped_min
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T09:21:57.260981+00:00
-- url     : https://prove2.me/submissions/6a2a7a79-90fa-411b-8ab9-5382fea73985

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_avram_root29_03_strict_up_event_iff_finite_weak_order

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Upper-first strict passage equals attaining the actual minimum stopped
clock with a finite upper exit time, excluding both clocks infinite. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (a x : ℝ) (ha : 0 < a) (ω : Ω) :
    twoSidedExitUpTime X (a - x) ω <
      twoSidedExitDownTime X (-x) ω ↔
    min (twoSidedExitUpTime X (a - x) ω)
        (twoSidedExitDownTime X (-x) ω) =
      twoSidedExitUpTime X (a - x) ω ∧
    twoSidedExitUpTime X (a - x) ω < ⊤ := by
  rw [avram_root29_03_strict_up_event_iff_finite_weak_order X a x ha ω]
  constructor
  · rintro ⟨hLe, hFin⟩
    exact ⟨min_eq_left hLe, hFin⟩
  · rintro ⟨hMin, hFin⟩
    exact ⟨(min_eq_left_iff).mp hMin, hFin⟩
