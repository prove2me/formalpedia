-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_h_gaussian_original_nu_halfclosed_band_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T23:28:59.832299+00:00
-- url     : https://prove2.me/submissions/e8da4fa9-a41e-4c85-8b85-dbb5fccdec9a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_negative_jump_truncation_measure_finite
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- The exact strict-one, inclusive-cutoff negative source band has a finite
signed compensator drift, including any atom at the cutoff. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ε : ℝ) (hε : 0 < ε) :
    IntegrableOn (fun z : ℝ => z) (Ioc (-1 : ℝ) (-ε)) X.ν := by
  have hrate : X.ν (Iic (-ε)) < ⊤ :=
    negative_jump_truncation_measure_finite X.ν X.ν_integrable ε hε
  have hsub : Ioc (-1 : ℝ) (-ε) ⊆ Iic (-ε) := by
    intro z hz
    exact hz.2
  have hfinite : X.ν (Ioc (-1 : ℝ) (-ε)) ≠ ⊤ :=
    ne_of_lt (lt_of_le_of_lt (measure_mono hsub) hrate)
  have hmeas : AEStronglyMeasurable (fun z : ℝ => z) X.ν :=
    measurable_id.aestronglyMeasurable
  have hbound : ∀ᵐ z ∂(X.ν.restrict (Ioc (-1 : ℝ) (-ε))),
      ‖(z : ℝ)‖ ≤ (1 : ℝ) := by
    apply ae_restrict_of_forall_mem measurableSet_Ioc
    intro z hz
    rw [Real.norm_eq_abs]
    apply abs_le.mpr
    constructor
    · linarith [hz.1]
    · linarith [hz.2, hε]
  exact X.ν.integrableOn_of_bounded hfinite hmeas hbound
