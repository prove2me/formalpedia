-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_phys110_original_BV_finite_activity_ruin_contact_band_mass_vanish
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T10:40:05.825419+00:00
-- url     : https://prove2.me/submissions/6ff0ff50-329d-453f-92de-16a0640a6855

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bvb_phys107_Standing_BV_negative_mark_singletons_null
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology

/-- For the original finite-activity BV Lévy measure, negative jump
marks in a shrinking neighbourhood of the ruin threshold have vanishing mass. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hStanding : X.Standing) (hBV : X.BoundedVariation)
    (hActivity : X.ν (Iio (0 : ℝ)) < ⊤) (a : ℝ) :
    Tendsto
      (fun δ : ℝ => (X.ν.restrict (Iio (0 : ℝ)))
        (Icc (-a - δ) (-a + δ)))
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ≥0∞)) := by
  let μ : Measure ℝ := X.ν.restrict (Iio (0 : ℝ))
  have hfinite : μ Set.univ < ⊤ := by
    simpa only [μ, Measure.restrict_apply_univ] using hActivity
  have hraw : X.ν ({-a} : Set ℝ) = 0 :=
    avram_bvb_phys107_Standing_BV_negative_mark_singletons_null
      X hStanding hBV (-a)
  have hatom : μ ({-a} : Set ℝ) = 0 := by
    have hle : μ ({-a} : Set ℝ) ≤ X.ν ({-a} : Set ℝ) :=
      Measure.restrict_apply_le (Iio (0 : ℝ)) ({-a} : Set ℝ)
    exact le_antisymm (by simpa [hraw] using hle) (by positivity)
  letI : IsFiniteMeasure μ := ⟨hfinite⟩
  simpa only [hatom] using
    (tendsto_measure_Icc_nhdsWithin_right' μ (-a))
