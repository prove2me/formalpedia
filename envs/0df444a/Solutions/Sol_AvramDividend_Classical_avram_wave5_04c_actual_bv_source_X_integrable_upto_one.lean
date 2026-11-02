-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_04c_actual_bv_source_X_integrable_upto_one
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T10:49:51.031455+00:00
-- url     : https://prove2.me/submissions/c9cb6cf0-65f3-477b-b70d-ae150258087f

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Tactic.Ring
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_actual_bv_residual_integrable_upto_one
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hX : X.Standing) (hBV : X.BoundedVariation)
    (t : ℝ≥0) (ht : t ≤ 1) :
    Integrable (X.X t) P := by
  letI : IsProbabilityMeasure P := X.isProbability
  have hR :
      Integrable (fun ω : Ω => (t : ℝ) * X.drift - X.X t ω) P :=
    avram_wave5_04c_actual_bv_residual_integrable_upto_one X hX hBV t ht
  have htemp := (integrable_const ((t : ℝ) * X.drift)).sub hR
  convert htemp using 1
  funext ω
  simp only [Pi.sub_apply]
  ring