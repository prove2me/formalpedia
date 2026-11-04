-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_g_radon_negative_band_compact_test_ext
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T13:37:00.892323+00:00
-- url     : https://prove2.me/submissions/10cf4319-d460-42ba-a4a3-feb7991ef054

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_g_radon_negative_band_finite_implies_locally_finite

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter
open scoped ENNReal

/-- On the negative half-line, finite separated-band masses and equality of
    compactly supported continuous test integrals identify Borel measures. -/
theorem solution
    (μ ν : Measure {x : ℝ // x < 0})
    (hμBand : ∀ (ε : ℝ), 0 < ε →
      μ {x : {x : ℝ // x < 0} | (x : ℝ) ≤ -ε} < ⊤)
    (hνBand : ∀ (ε : ℝ), 0 < ε →
      ν {x : {x : ℝ // x < 0} | (x : ℝ) ≤ -ε} < ⊤)
    (hTests : ∀ (f : CompactlySupportedContinuousMap {x : ℝ // x < 0} ℝ),
      (∫ x, f x ∂μ) = (∫ x, f x ∂ν)) :
    μ = ν := by
  letI : LocallyCompactSpace {x : ℝ // x < 0} :=
    (isOpen_Iio : IsOpen (Iio (0 : ℝ))).locallyCompactSpace
  letI : SigmaCompactSpace {x : ℝ // x < 0} :=
    sigmaCompactSpace_of_locallyCompact_secondCountable
  letI : IsLocallyFiniteMeasure μ :=
    AvramDividend.Classical.avram_p2_g_radon_negative_band_finite_implies_locally_finite
      μ hμBand
  letI : IsLocallyFiniteMeasure ν :=
    AvramDividend.Classical.avram_p2_g_radon_negative_band_finite_implies_locally_finite
      ν hνBand
  haveI : μ.Regular :=
    Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure μ
  haveI : ν.Regular :=
    Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure ν
  exact Measure.ext_of_integral_eq_on_compactlySupported hTests
