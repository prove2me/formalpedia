-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_c_borel_all_negative_rate_from_dense_cutoff_tests
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T14:56:44.084321+00:00
-- url     : https://prove2.me/submissions/59c347d4-7640-4ae9-aaad-77f1d669100f

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_c_borel_original_separated_rate_from_dense_tests
import Theorems.Thm_AvramDividend_Classical_avram_p2_c_borel_harmonic_negative_band_exhaustion
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_source_borel_rate_from_separated_monotone_bands

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- Dense analytic halfline tests at harmonic cutoffs imply the full original negative rate. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (B : Set ℝ) (hB : MeasurableSet B) (hBneg : B ⊆ Iio (0 : ℝ))
    (D : Set ℝ) (hDense : Dense D)
    (hTests : ∀ (n : ℕ) (a : ℝ), a ∈ D →
      (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ (Iic a ∩ Iic (-(1 / ((n : ℝ) + 1))))) ∂P) =
        (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν (Iic a ∩ Iic (-(1 / ((n : ℝ) + 1)))))) :
    (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B) ∂P) = (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B) := by
  obtain ⟨hBm, hBmono, hCover, hSep⟩ :=
    avram_p2_c_borel_harmonic_negative_band_exhaustion B hB hBneg
  apply avram_wave7_01_source_borel_rate_from_separated_monotone_bands
    X s t hst B
    (fun n => B ∩ Iic (-(1 / ((n : ℝ) + 1))))
    hBm hBmono hCover hSep
  intro n
  have hnPos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
  exact avram_p2_c_borel_original_separated_rate_from_dense_tests
    X s t hst (1 / ((n : ℝ) + 1)) hnPos
    (B ∩ Iic (-(1 / ((n : ℝ) + 1))))
    (hB.inter measurableSet_Iic) inter_subset_right
    D hDense (hTests n)
