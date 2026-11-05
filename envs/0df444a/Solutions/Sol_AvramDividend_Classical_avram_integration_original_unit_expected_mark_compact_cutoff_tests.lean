-- Prove2me | solution 1 for AvramDividend.Classical.avram_integration_original_unit_expected_mark_compact_cutoff_tests
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T09:31:29.383999+00:00
-- url     : https://prove2.me/submissions/cae25122-6eaa-49f4-9362-03bec847ecc9

import Mathlib.Probability.Process.Filtration
import Mathlib.Topology.ContinuousMap.CompactlySupported
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_assist_original_signed_compact_intensity_eq_nu_tests
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_assist_signed_tests_determine_negative_borel
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_separated_borel_nu_finite

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- Compact-cutoff tests agree by identifying original marked intensity on
separated negative Borel sets using proved signed compact-test uniqueness. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ε : ℝ) (hε : 0 < ε)
    (ρ : Measure ℝ)
    (hρ : ∀ B : Set ℝ, MeasurableSet B →
      ρ B = (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 (1 : ℝ≥0) ×ˢ B) ∂P))
    (hρfinite : ρ (Iic (-ε)) ≠ ⊤) :
    ∀ g : CompactlySupportedContinuousMap ℝ ℝ,
      (∫ y : ℝ, g y ∂(ρ.restrict (Iic (-ε)))) =
        (∫ y : ℝ, g y ∂(X.ν.restrict (Iic (-ε)))) := by
  letI : IsProbabilityMeasure P := X.isProbability
  obtain ⟨σ, hRate, hSigned, hσBand, _, _⟩ :=
    avram_p2_a_assist_original_signed_compact_intensity_eq_nu_tests P X
  have hρσ : ρ = σ := by
    apply Measure.ext
    intro B hB
    calc
      ρ B = _ := hρ B hB
      _ = σ B := by simpa using hRate (1 : ℝ≥0) B hB
  have hνBand : ∀ δ : ℝ, 0 < δ →
      (X.ν.restrict (Iio (0 : ℝ))) (Iic (-δ)) < ⊤ := by
    intro δ hδ
    have hSep : Iic (-δ) ⊆ Iio (0 : ℝ) := by
      intro y hy
      change y < 0
      have hy' : y ≤ -δ := hy
      linarith
    have hFin : X.ν (Iic (-δ)) < ⊤ :=
      avram_p2_a_zero_rate_separated_borel_nu_finite
        X (Iic (-δ)) measurableSet_Iic δ hδ Subset.rfl
    calc
      (X.ν.restrict (Iio (0 : ℝ))) (Iic (-δ)) =
          X.ν (Iic (-δ) ∩ Iio (0 : ℝ)) :=
            Measure.restrict_apply measurableSet_Iic
      _ = X.ν (Iic (-δ)) :=
        congrArg X.ν (inter_eq_left.mpr hSep)
      _ < ⊤ := hFin
  have hCut0 : Iic (-ε) ⊆ Iio (0 : ℝ) := by
    intro y hy
    change y < 0
    have hy' : y ≤ -ε := hy
    linarith
  have hBorel (B : Set ℝ) (hB : MeasurableSet B)
      (hBsep : B ⊆ Iic (-ε)) : ρ B = X.ν B := by
    have hSep0 : B ⊆ Iio (0 : ℝ) := hBsep.trans hCut0
    have hEq :=
      avram_p2_a_assist_signed_tests_determine_negative_borel
        σ (X.ν.restrict (Iio (0 : ℝ))) hσBand hνBand
        hSigned B hB ε hε hBsep
    calc
      ρ B = σ B := congrArg (fun μ : Measure ℝ => μ B) hρσ
      _ = (X.ν.restrict (Iio (0 : ℝ))) B := hEq
      _ = X.ν B := by
        rw [Measure.restrict_apply hB, inter_eq_left.mpr hSep0]
  have hRestrict :
      ρ.restrict (Iic (-ε)) = X.ν.restrict (Iic (-ε)) := by
    apply Measure.ext
    intro B hB
    calc
      (ρ.restrict (Iic (-ε))) B = ρ (B ∩ Iic (-ε)) :=
        Measure.restrict_apply hB
      _ = X.ν (B ∩ Iic (-ε)) :=
        hBorel _ (hB.inter measurableSet_Iic) inter_subset_right
      _ = (X.ν.restrict (Iic (-ε))) B :=
        (Measure.restrict_apply hB).symm
  intro g
  rw [hRestrict]
