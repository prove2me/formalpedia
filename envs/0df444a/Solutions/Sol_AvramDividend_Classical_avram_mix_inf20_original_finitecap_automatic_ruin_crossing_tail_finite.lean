-- Prove2me | solution 1 for AvramDividend.Classical.avram_mix_inf20_original_finitecap_automatic_ruin_crossing_tail_finite
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T16:26:07.780808+00:00
-- url     : https://prove2.me/submissions/e43851a6-17fa-4d2b-8202-5f4c14a650f0

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_negative_levy_mark_tail_finite_mass_at_every_small_threshold
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option autoImplicit false

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hν : (∫⁻ z : ℝ,
      ENNReal.ofReal (min (1 : ℝ) (z ^ 2)) ∂X.ν) < ⊤)
    (C : ℝ≥0∞) (hFinite : C ≠ ⊤) (hCapPos : 0 < C.toReal)
    (y : ℝ) (hy : C.toReal < y) :
    X.ν {z : ℝ | y + z < 0} < ⊤ := by
  let δ : ℝ := min C.toReal 1
  have hδ : 0 < δ := lt_min hCapPos (by norm_num)
  have hδone : δ ≤ 1 := min_le_right _ _
  have hδcap : δ ≤ C.toReal := min_le_left _ _
  have htail :=
    avram_wave7_02_original_negative_levy_mark_tail_finite_mass_at_every_small_threshold
      X.ν hν δ hδ hδone
  have hsubset : {z : ℝ | y + z < 0} ⊆ Iic (-δ) := by
    intro z hz
    change z ≤ -δ
    have hbad : y + z < 0 := hz
    linarith
  exact lt_of_le_of_lt (measure_mono hsubset) htail
