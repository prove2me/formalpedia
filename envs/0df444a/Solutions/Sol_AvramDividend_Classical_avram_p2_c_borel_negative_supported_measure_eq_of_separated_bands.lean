-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_c_borel_negative_supported_measure_eq_of_separated_bands
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T21:23:40.14363+00:00
-- url     : https://prove2.me/submissions/3bf507cd-1276-41a1-b85d-a3a5566a9495

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_c_borel_harmonic_negative_band_exhaustion
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- Negative-supported sigma-additive intensities agree if all strictly separated
Borel bands have the same masses, with no finiteness premise. -/
theorem solution
    (μ ν : Measure ℝ)
    (hμneg : ∀ B : Set ℝ, MeasurableSet B →
      μ B = μ (B ∩ Iio (0 : ℝ)))
    (hνneg : ∀ B : Set ℝ, MeasurableSet B →
      ν B = ν (B ∩ Iio (0 : ℝ)))
    (hBands : ∀ (B : Set ℝ), MeasurableSet B →
      ∀ ε : ℝ, 0 < ε → B ⊆ Iic (-ε) → μ B = ν B) :
    μ = ν := by
  apply Measure.ext
  intro B hB
  let D : Set ℝ := B ∩ Iio (0 : ℝ)
  have hDm : MeasurableSet D := hB.inter measurableSet_Iio
  have hDneg : D ⊆ Iio (0 : ℝ) := inter_subset_right
  obtain ⟨hBm, hMono, hCover, hSep⟩ :=
    avram_p2_c_borel_harmonic_negative_band_exhaustion D hDm hDneg
  have hμcont :
      μ D = ⨆ n : ℕ, μ (D ∩ Iic (-(1 / ((n : ℝ) + 1)))) := by
    calc
      μ D = μ (⋃ n : ℕ, D ∩ Iic (-(1 / ((n : ℝ) + 1)))) := by rw [hCover]
      _ = ⨆ n : ℕ, μ (D ∩ Iic (-(1 / ((n : ℝ) + 1)))) :=
        hMono.measure_iUnion
  have hνcont :
      ν D = ⨆ n : ℕ, ν (D ∩ Iic (-(1 / ((n : ℝ) + 1)))) := by
    calc
      ν D = ν (⋃ n : ℕ, D ∩ Iic (-(1 / ((n : ℝ) + 1)))) := by rw [hCover]
      _ = ⨆ n : ℕ, ν (D ∩ Iic (-(1 / ((n : ℝ) + 1)))) :=
        hMono.measure_iUnion
  calc
    μ B = μ D := hμneg B hB
    _ = ⨆ n : ℕ, μ (D ∩ Iic (-(1 / ((n : ℝ) + 1)))) := hμcont
    _ = ⨆ n : ℕ, ν (D ∩ Iic (-(1 / ((n : ℝ) + 1)))) := by
      apply iSup_congr
      intro n
      obtain ⟨ε, hε, hSub⟩ := hSep n
      exact hBands _ (hBm n) ε hε hSub
    _ = ν D := hνcont.symm
    _ = ν B := (hνneg B hB).symm
