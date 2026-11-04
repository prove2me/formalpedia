-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_c_borel_stationary_expected_mark_additive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T17:49:52.129953+00:00
-- url     : https://prove2.me/submissions/40e76b17-02e1-40ea-b5be-8d3129756cb9

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Theorems.Thm_AvramDividend_Classical_avram_p2_c_borel_time_rectangle_split

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- Pointwise rectangle additivity and stationary expected increments give an
additive nonnegative expected marked-count function of elapsed time. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (M : Ω → Measure (ℝ≥0 × ℝ))
    (B : Set ℝ) (hB : MeasurableSet B)
    (s t : ℝ≥0)
    (hMeas : Measurable (fun ω => M ω (Ioc 0 s ×ˢ B)))
    (hShift :
      (∫⁻ ω, M ω (Ioc s (s + t) ×ˢ B) ∂P) =
      (∫⁻ ω, M ω (Ioc 0 t ×ˢ B) ∂P)) :
    (∫⁻ ω, M ω (Ioc 0 (s + t) ×ˢ B) ∂P) =
      (∫⁻ ω, M ω (Ioc 0 s ×ˢ B) ∂P) +
      (∫⁻ ω, M ω (Ioc 0 t ×ˢ B) ∂P) := by
  have hPoint (ω : Ω) :
      M ω (Ioc 0 (s + t) ×ˢ B) =
        M ω (Ioc 0 s ×ˢ B) + M ω (Ioc s (s + t) ×ˢ B) :=
    avram_p2_c_borel_time_rectangle_split (M ω) 0 s (s + t)
      (by simp) (by simp) B hB
  calc
    (∫⁻ ω, M ω (Ioc 0 (s + t) ×ˢ B) ∂P) =
        (∫⁻ ω, M ω (Ioc 0 s ×ˢ B) +
          M ω (Ioc s (s + t) ×ˢ B) ∂P) := by
      refine lintegral_congr ?_
      intro ω
      exact hPoint ω
    _ = (∫⁻ ω, M ω (Ioc 0 s ×ˢ B) ∂P) +
          (∫⁻ ω, M ω (Ioc s (s + t) ×ˢ B) ∂P) :=
      lintegral_add_left hMeas _
    _ = (∫⁻ ω, M ω (Ioc 0 s ×ˢ B) ∂P) +
          (∫⁻ ω, M ω (Ioc 0 t ×ˢ B) ∂P) := by
      rw [hShift]
