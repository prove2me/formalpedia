-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave8_22_actual_physical_BV_C1_local_negative_mark_tail_from_levy_energy
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T10:43:44.670569+00:00
-- url     : https://prove2.me/submissions/2a71311c-d2cb-47dc-9c1a-8b053fdac897

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_negative_levy_mark_tail_finite_mass_at_every_small_threshold
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The genuine negative mark intensity beyond half the compact positive reserve is finite. -/
theorem solution
  {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  {𝓕 : Filtration ℝ≥0 mΩ}
  (X : SpectrallyNegativeLevy P 𝓕)
  (hν : (∫⁻ z : ℝ, ENNReal.ofReal (min (1 : ℝ) (z ^ 2)) ∂X.ν) < ⊤)
  (a : ℝ) (ha : 0 < a) (ha2 : a ≤ 2) :
  X.ν (Iic (-(a / 2))) < ⊤ := by
  have hpos : 0 < a / 2 := by linarith
  have hone : a / 2 ≤ 1 := by linarith
  exact avram_wave7_02_original_negative_levy_mark_tail_finite_mass_at_every_small_threshold
    X.ν hν (a / 2) hpos hone
