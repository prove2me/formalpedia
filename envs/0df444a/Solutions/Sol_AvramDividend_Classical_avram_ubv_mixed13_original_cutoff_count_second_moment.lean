-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_mixed13_original_cutoff_count_second_moment
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T00:36:42.900979+00:00
-- url     : https://prove2.me/submissions/56eedaca-ee56-4302-aff3-a5f4c05a1dc1

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f2_original_band_count_factorial_moment_exact
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_cutoff_marked_count_L1_auto

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The original physical full-cutoff negative marked count has a second
moment, obtained directly from its first and factorial moments. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (n : ℕ) :
    let B : Set ℝ := Iic (-(1 / ((n : ℝ) + 1)))
    let N : Ω → ℝ≥0∞ := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ B)
    Integrable (fun ω => ((N ω).toReal) ^ 2) P := by
  intro B N
  have hFact :
      Integrable (fun ω => (N ω).toReal * ((N ω).toReal - 1)) P :=
    (avram_p4_f2_original_band_count_factorial_moment_exact X T n).1
  have hMean : Integrable (fun ω => (N ω).toReal) P :=
    avram_p4_f_assembly_original_cutoff_marked_count_L1_auto X T n
  have hAdd := hFact.add hMean
  have hEq :
      (fun ω => ((N ω).toReal) ^ 2) =
      (fun ω => (N ω).toReal * ((N ω).toReal - 1) + (N ω).toReal) := by
    funext ω
    ring
  rw [hEq]
  exact hAdd
