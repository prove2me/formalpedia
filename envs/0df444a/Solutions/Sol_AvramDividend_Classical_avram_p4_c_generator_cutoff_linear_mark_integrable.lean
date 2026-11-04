-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_c_generator_cutoff_linear_mark_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T08:00:11.983166+00:00
-- url     : https://prove2.me/submissions/5955a005-34d5-44a8-bf25-347794145ebf

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_negative_jump_truncation_measure_finite

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ε : ℝ) (hε : 0 < ε) :
    IntegrableOn (fun z : ℝ => z) (Ioo (-1 : ℝ) (-ε)) X.ν := by
  have hrate : X.ν (Iic (-ε)) < ⊤ :=
    negative_jump_truncation_measure_finite X.ν X.ν_integrable ε hε
  have hsub : Ioo (-1 : ℝ) (-ε) ⊆ Iic (-ε) := by
    intro z hz
    exact le_of_lt hz.2
  have hfinite : X.ν (Ioo (-1 : ℝ) (-ε)) ≠ ⊤ :=
    ne_of_lt (lt_of_le_of_lt (measure_mono hsub) hrate)
  have hmeas : AEStronglyMeasurable (fun z : ℝ => z) X.ν :=
    measurable_id.aestronglyMeasurable
  have hbound : ∀ᵐ z ∂(X.ν.restrict (Ioo (-1 : ℝ) (-ε))),
      ‖(z : ℝ)‖ ≤ (1 : ℝ) := by
    apply ae_restrict_of_forall_mem measurableSet_Ioo
    intro z hz
    rw [Real.norm_eq_abs]
    apply abs_le.mpr
    constructor
    · linarith [hz.1]
    · linarith [hz.2, hε]
  exact X.ν.integrableOn_of_bounded hfinite hmeas hbound
