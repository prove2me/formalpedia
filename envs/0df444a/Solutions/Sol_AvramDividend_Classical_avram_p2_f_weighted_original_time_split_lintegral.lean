-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_f_weighted_original_time_split_lintegral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T18:57:48.219613+00:00
-- url     : https://prove2.me/submissions/b63a54ca-7c45-415b-a9f7-107a6de8a509

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_original_time_split_pathwise
import Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_original_intrinsic_rectangle_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- Genuine original-process source expected jump count is additive
across adjacent future windows under any measurable ENNReal path weight. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s a b : ℝ≥0) (B : Set ℝ) (hB : MeasurableSet B)
    (H : Ω → ℝ≥0∞) (hH : Measurable H) :
    (∫⁻ ω, H ω * ((Measure.count.restrict {v : ℝ≥0 |
      0 < v ∧ X.X v ω -
        Function.leftLim (fun w : ℝ≥0 => X.X w ω) v ≠ 0}).map
      (fun v : ℝ≥0 => (v,
        X.X v ω - Function.leftLim (fun w : ℝ≥0 => X.X w ω) v)))
      (Ioc s (s + (a + b)) ×ˢ B) ∂P) =
    (∫⁻ ω, H ω * ((Measure.count.restrict {v : ℝ≥0 |
      0 < v ∧ X.X v ω -
        Function.leftLim (fun w : ℝ≥0 => X.X w ω) v ≠ 0}).map
      (fun v : ℝ≥0 => (v,
        X.X v ω - Function.leftLim (fun w : ℝ≥0 => X.X w ω) v)))
      (Ioc s (s + a) ×ˢ B) ∂P) +
    (∫⁻ ω, H ω * ((Measure.count.restrict {v : ℝ≥0 |
      0 < v ∧ X.X v ω -
        Function.leftLim (fun w : ℝ≥0 => X.X w ω) v ≠ 0}).map
      (fun v : ℝ≥0 => (v,
        X.X v ω - Function.leftLim (fun w : ℝ≥0 => X.X w ω) v)))
      (Ioc (s + a) ((s + a) + b) ×ˢ B) ∂P) := by
  let N : Set (ℝ≥0 × ℝ) → Ω → ℝ≥0∞ := fun D ω =>
    ((Measure.count.restrict {v : ℝ≥0 |
      0 < v ∧ X.X v ω -
        Function.leftLim (fun w : ℝ≥0 => X.X w ω) v ≠ 0}).map
      (fun v : ℝ≥0 => (v,
        X.X v ω - Function.leftLim (fun w : ℝ≥0 => X.X w ω) v)))
      D
  have hPart (ω : Ω) :
      N (Ioc s (s + (a + b)) ×ˢ B) ω =
        N (Ioc s (s + a) ×ˢ B) ω +
          N (Ioc (s + a) ((s + a) + b) ×ˢ B) ω := by
    have hst : s ≤ s + a :=
      le_add_of_nonneg_right (show (0 : ℝ≥0) ≤ a from zero_le)
    have htu : s + a ≤ s + (a + b) := by
      simpa only [add_assoc] using
        (le_add_of_nonneg_right (show (0 : ℝ≥0) ≤ b from zero_le) :
          s + a ≤ (s + a) + b)
    have h := avram_p2_f_weighted_original_time_split_pathwise
      X s (s + a) (s + (a + b)) hst htu B hB ω
    simpa only [N, add_assoc] using h
  have hMeasFirst : Measurable
      (fun ω => H ω * N (Ioc s (s + a) ×ˢ B) ω) :=
    hH.mul (avram_p2_f_weighted_original_intrinsic_rectangle_measurable
      X s a B hB)
  change (∫⁻ ω, H ω * N (Ioc s (s + (a + b)) ×ˢ B) ω ∂P) =
    (∫⁻ ω, H ω * N (Ioc s (s + a) ×ˢ B) ω ∂P) +
    (∫⁻ ω, H ω * N (Ioc (s + a) ((s + a) + b) ×ˢ B) ω ∂P)
  calc
    (∫⁻ ω, H ω * N (Ioc s (s + (a + b)) ×ˢ B) ω ∂P) =
      (∫⁻ ω, H ω *
        (N (Ioc s (s + a) ×ˢ B) ω +
          N (Ioc (s + a) ((s + a) + b) ×ˢ B) ω) ∂P) := by
            congr 1
            funext ω
            rw [hPart ω]
    _ = (∫⁻ ω,
      H ω * N (Ioc s (s + a) ×ˢ B) ω +
        H ω * N (Ioc (s + a) ((s + a) + b) ×ˢ B) ω ∂P) := by
          congr 1
          funext ω
          exact mul_add _ _ _
    _ = _ := MeasureTheory.lintegral_add_left hMeasFirst _
