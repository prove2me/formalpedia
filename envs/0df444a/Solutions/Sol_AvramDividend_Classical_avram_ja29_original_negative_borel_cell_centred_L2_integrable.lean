-- Prove2me | solution 1 for AvramDividend.Classical.avram_ja29_original_negative_borel_cell_centred_L2_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T18:52:45.274587+00:00
-- url     : https://prove2.me/submissions/0e975450-20f4-43af-8f5c-d43ddef4cdc9

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_original_negative_borel_cell_centred_L2_from_full_band
import Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_separated_borel_cell_compensated_mean_zero_auto

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Original arbitrary separated Borel cell has centred L1 and L2 source
certificates, without assuming independent auxiliary noise. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (cut : ℕ)
    (B : Set ℝ) (hB : MeasurableSet B)
    (hSep : B ⊆ Iic (-(1 / ((cut : ℝ) + 1)))) :
    let N : Ω → ℝ≥0∞ := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ B)
    let r : ℝ := ((T : ℝ≥0∞) * X.ν B).toReal
    Integrable (fun ω => (N ω).toReal - r) P ∧
    (∫ ω, (N ω).toReal - r ∂P) = 0 ∧
    Integrable (fun ω => ((N ω).toReal - r) ^ 2) P := by
  letI : IsProbabilityMeasure P := X.isProbability
  let N : Ω → ℝ≥0∞ := fun ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 T ×ˢ B)
  let r : ℝ := ((T : ℝ≥0∞) * X.ν B).toReal
  change Integrable (fun ω => (N ω).toReal - r) P ∧
    (∫ ω, (N ω).toReal - r ∂P) = 0 ∧
    Integrable (fun ω => ((N ω).toReal - r) ^ 2) P
  have hε : 0 < (1 / ((cut : ℝ) + 1)) := by positivity
  have hMean :
      Integrable (fun ω => (N ω).toReal - r) P ∧
      (∫ ω, (N ω).toReal - r ∂P) = 0 := by
    simpa only [tsub_zero] using
      (avram_p4_f3_original_separated_borel_cell_compensated_mean_zero_auto
        X 0 T (show (0 : ℝ≥0) ≤ T from zero_le) B hB
        (1 / ((cut : ℝ) + 1)) hε hSep)
  have hL2 : MemLp (fun ω => (N ω).toReal - r) 2 P := by
    simpa only [tsub_zero] using
      (avram_p4_s3_original_negative_borel_cell_centred_L2_from_full_band
        X T cut 0 T (show (0 : ℝ≥0) ≤ T from zero_le)
        le_rfl B hB hSep)
  exact ⟨hMean.1, hMean.2,
    (memLp_two_iff_integrable_sq hL2.aestronglyMeasurable).1 hL2⟩
