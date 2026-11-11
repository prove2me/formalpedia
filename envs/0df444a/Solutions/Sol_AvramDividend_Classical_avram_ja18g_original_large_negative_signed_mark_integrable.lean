-- Prove2me | solution 1 for AvramDividend.Classical.avram_ja18g_original_large_negative_signed_mark_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T02:51:44.092595+00:00
-- url     : https://prove2.me/submissions/4f4a85dd-67f9-479c-a0f1-403b8d0fc5a5

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ja18p_large_negative_mark_firstmoment_standing

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Original signed negative-large marks are L1 from the proved first-moment estimate. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) :
    IntegrableOn (fun z : ℝ => z) (Iic (-1 : ℝ)) X.ν := by
  have hFin : (∫⁻ z in Iic (-1 : ℝ), ‖z‖ₑ ∂X.ν) < ⊤ := by
    simpa only [Real.enorm_eq_ofReal_abs] using
      (avram_ja18p_large_negative_mark_firstmoment_standing X hX)
  exact ⟨stronglyMeasurable_id.aestronglyMeasurable, hFin⟩
