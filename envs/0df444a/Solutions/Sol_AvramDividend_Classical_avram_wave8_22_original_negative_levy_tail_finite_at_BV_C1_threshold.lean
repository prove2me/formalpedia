-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave8_22_original_negative_levy_tail_finite_at_BV_C1_threshold
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T23:59:17.978486+00:00
-- url     : https://prove2.me/submissions/0e2da759-a13d-4ccb-a9e8-af3bb64018df

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Tactic.Linarith
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_negative_levy_mark_tail_finite_mass_at_every_small_threshold
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The original Lévy quadratic energy makes the BV C¹ negative-jump localisation tail finite. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (a : ℝ) (ha : 0 < a) (ha2 : a ≤ 2) :
    X.ν (Iic (-a / 2)) < ⊤ := by
  have hTail : X.ν (Iic (-(a / 2))) < ⊤ :=
    avram_wave7_02_original_negative_levy_mark_tail_finite_mass_at_every_small_threshold
      X.ν X.ν_integrable (a / 2) (by linarith) (by linarith)
  simpa only [neg_div] using hTail
