-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_f_weighted_original_finite_simple_integral_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T14:57:43.976189+00:00
-- url     : https://prove2.me/submissions/20fe1a2c-36d7-44ac-ad85-6f91c50d6e1a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_original_intrinsic_rectangle_measurable
import Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_random_measure_finite_simple_integral_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- A genuine finite predictable-simple intrinsic Lévy jump integral is
ambient measurable without assuming a new random kernel or ν rate. -/
theorem solution
    {Ω ι : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (S : Finset ι) (s T : ι → ℝ≥0)
    (B : ι → Set ℝ) (hB : ∀ i ∈ S, MeasurableSet (B i))
    (H : ι → Ω → ℝ≥0∞)
    (hH : ∀ i ∈ S, Measurable[𝓕 (s i)] (H i)) :
    Measurable (fun ω =>
      (∫⁻ p, S.sum (fun i => (Ioc (s i) (s i + T i) ×ˢ B i).indicator (fun _ => H i ω) p) ∂((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))))) := by
  exact avram_p2_f_weighted_random_measure_finite_simple_integral_measurable
    (fun ω => ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))) S
    (fun i => (Ioc (s i) (s i + T i) ×ˢ B i))
    (by
      intro i hi
      exact measurableSet_Ioc.prod (hB i hi))
    H
    (by
      intro i hi
      exact (hH i hi).mono (𝓕.le (s i)) le_rfl)
    (by
      intro i hi
      exact avram_p2_f_weighted_original_intrinsic_rectangle_measurable
        X (s i) (T i) (B i) (hB i hi))
