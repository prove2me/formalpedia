-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_c_borel_original_intrinsic_rate_restricted_nu_of_unit_separated_bands
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T22:08:09.96039+00:00
-- url     : https://prove2.me/submissions/ac60ce16-40d6-4fe1-9821-e98c6bfa352d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_c_borel_original_intrinsic_intensity_measure_complete
import Theorems.Thm_AvramDividend_Classical_avram_p2_c_borel_negative_supported_measure_eq_of_separated_bands
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- Source-original unit separated rates identify the complete original intensity
with the NEGATIVE restriction of ν, without a separate ν support hypothesis. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hUnitSeparated : ∀ (B : Set ℝ), MeasurableSet B →
      ∀ ε : ℝ, 0 < ε → B ⊆ Iic (-ε) →
        (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 (1 : ℝ≥0) ×ˢ B) ∂P) = X.ν B) :
    ∀ (T : ℝ≥0) (B : Set ℝ), MeasurableSet B →
      (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ B) ∂P) = (T : ℝ≥0∞) *
          X.ν (B ∩ Iio (0 : ℝ)) := by
  obtain ⟨markRate, hRate, _, hSupp, _⟩ :=
    avram_p2_c_borel_original_intrinsic_intensity_measure_complete X
  let νneg : Measure ℝ := X.ν.restrict (Iio (0 : ℝ))
  have hνsupp : ∀ B : Set ℝ, MeasurableSet B →
      νneg B = νneg (B ∩ Iio (0 : ℝ)) := by
    intro B hB
    calc
      νneg B = X.ν (B ∩ Iio (0 : ℝ)) :=
        Measure.restrict_apply hB
      _ = X.ν ((B ∩ Iio (0 : ℝ)) ∩ Iio (0 : ℝ)) := by
        congr 1
        ext x
        simp
      _ = νneg (B ∩ Iio (0 : ℝ)) :=
        (Measure.restrict_apply (hB.inter measurableSet_Iio)).symm
  have hBandEq :
      ∀ (B : Set ℝ), MeasurableSet B →
        ∀ ε : ℝ, 0 < ε → B ⊆ Iic (-ε) →
          markRate B = νneg B := by
    intro B hB ε hε hSep
    have hAtOne := hRate (1 : ℝ≥0) B hB
    have hUnit : (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 (1 : ℝ≥0) ×ˢ B) ∂P) = markRate B := by
      simpa using hAtOne
    have hCut : -ε < (0 : ℝ) := by linarith
    have hIncl : B ⊆ Iio (0 : ℝ) := by
      intro x hx
      exact lt_of_le_of_lt (hSep hx) hCut
    have hBEq : B ∩ Iio (0 : ℝ) = B :=
      Set.inter_eq_left.mpr hIncl
    have hRestr : νneg B = X.ν B := by
      calc
        νneg B = X.ν (B ∩ Iio (0 : ℝ)) :=
          Measure.restrict_apply hB
        _ = X.ν B := congrArg X.ν hBEq
    exact (hUnit.symm.trans (hUnitSeparated B hB ε hε hSep)).trans hRestr.symm
  have hEq : markRate = νneg :=
    avram_p2_c_borel_negative_supported_measure_eq_of_separated_bands
      markRate νneg hSupp hνsupp hBandEq
  intro T B hB
  calc
    (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ B) ∂P) =
        (T : ℝ≥0∞) * markRate B := hRate T B hB
    _ = (T : ℝ≥0∞) * νneg B := by rw [hEq]
    _ = (T : ℝ≥0∞) * X.ν (B ∩ Iio (0 : ℝ)) := by
      exact congrArg (fun z : ℝ≥0∞ => (T : ℝ≥0∞) * z)
        (Measure.restrict_apply hB)
