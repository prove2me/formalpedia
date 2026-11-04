-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_b_smalljump_original_marked_event_interval_lintegral_split
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T21:29:02.996219+00:00
-- url     : https://prove2.me/submissions/1f709e45-05a8-48c6-bd82-52f12e502e03

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_marked_interval_split
import Theorems.Thm_AvramDividend_Classical_avram_p2_d_future_intrinsic_marked_rectangle_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped ENNReal NNReal

/-- The genuine intrinsic marked Lévy jump counts split in expectation
after restriction to any original-space event, without assuming a compensator. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s r t : ℝ≥0) (hsr : s ≤ r) (hrt : r ≤ t)
    (B : Set ℝ) (hB : MeasurableSet B) (A : Set Ω) :
    (∫⁻ ω in A, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B) ∂P) =
      (∫⁻ ω in A, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s r ×ˢ B) ∂P) +
      (∫⁻ ω in A, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc r t ×ˢ B) ∂P) := by
  let N (a b : ℝ≥0) (ω : Ω) : ℝ≥0∞ :=
    (Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))
      (Ioc a b ×ˢ B)
  have hSplit (ω : Ω) :
      N s t ω = N s r ω + N r t ω := by
    simpa only [N] using
      (avram_p4_b_smalljump_original_marked_interval_split
        X ω s r t hsr hrt B hB)
  have hMeas : Measurable (N s r) := by
    simpa only [N] using
      (avram_p2_d_future_intrinsic_marked_rectangle_measurable X s r B hB)
  change (∫⁻ ω in A, N s t ω ∂P) =
    (∫⁻ ω in A, N s r ω ∂P) + (∫⁻ ω in A, N r t ω ∂P)
  calc
    (∫⁻ ω in A, N s t ω ∂P) =
      (∫⁻ ω in A, N s r ω + N r t ω ∂P) := by
        apply lintegral_congr
        intro ω
        exact hSplit ω
    _ = (∫⁻ ω in A, N s r ω ∂P) +
      (∫⁻ ω in A, N r t ω ∂P) :=
        lintegral_add_left hMeas _
