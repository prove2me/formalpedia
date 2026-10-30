-- Prove2me | solution 1 for AvramDividend.Classical.avram_root29_03_exit_discount_at_finite_stopped_min
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T09:27:05.28598+00:00
-- url     : https://prove2.me/submissions/12f6f0ce-6637-45a0-89d5-6a2830c7d788

import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_avram_root29_03_strict_up_event_iff_finite_weak_order

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The true strict upper-first q-discount can be evaluated at the finite
minimum of the original Lévy process's two strict passage clocks. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q a x : ℝ) (ha : 0 < a) :
    twoSidedExitExpectation X q a x =
    (∫⁻ ω,
      if twoSidedExitUpTime X (a - x) ω ≤ twoSidedExitDownTime X (-x) ω ∧
          twoSidedExitUpTime X (a - x) ω < ⊤ then
        ENNReal.ofReal (Real.exp (-(q * ENNReal.toReal
          (min (twoSidedExitUpTime X (a - x) ω)
               (twoSidedExitDownTime X (-x) ω)))))
      else 0 ∂P) := by
  unfold twoSidedExitExpectation
  apply lintegral_congr
  intro ω
  by_cases hOrder : twoSidedExitUpTime X (a - x) ω <
      twoSidedExitDownTime X (-x) ω
  · have hWeak : twoSidedExitUpTime X (a - x) ω ≤
        twoSidedExitDownTime X (-x) ω ∧
        twoSidedExitUpTime X (a - x) ω < ⊤ :=
      (avram_root29_03_strict_up_event_iff_finite_weak_order
        X a x ha ω).mp hOrder
    have hMin : min (twoSidedExitUpTime X (a - x) ω)
        (twoSidedExitDownTime X (-x) ω) =
        twoSidedExitUpTime X (a - x) ω :=
      min_eq_left hWeak.1
    simp only [if_pos hOrder, if_pos hWeak, hMin]
  · have hNotWeak : ¬ (twoSidedExitUpTime X (a - x) ω ≤
        twoSidedExitDownTime X (-x) ω ∧
        twoSidedExitUpTime X (a - x) ω < ⊤) := by
      intro hWeak
      exact hOrder
        ((avram_root29_03_strict_up_event_iff_finite_weak_order
          X a x ha ω).mpr hWeak)
    simp only [if_neg hOrder, if_neg hNotWeak]
