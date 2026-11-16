-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_obstruction_original_zero_negative_marks_jump_series_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T09:38:25.694631+00:00
-- url     : https://prove2.me/submissions/99bbe6b2-d838-4d53-80c0-64344d4dd929

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bvb_phys73_original_zero_negative_mark_count_no_negative_jumps
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_levy_jumpmark_nonpositive
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (T : ℝ≥0)
    (hZero : ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ (X.X u ω - Function.leftLim
          (fun v : ℝ≥0 => X.X v ω) u) ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 T ×ˢ Iio (0 : ℝ)) = 0) :
    ∀ t : ℝ≥0, t ≤ T →
      (∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
        Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
          else 0) = 0 := by
  intro t ht
  have hn := avram_bvb_phys73_original_zero_negative_mark_count_no_negative_jumps
    X ω T hZero
  have hp := avram_wave4_04a_actual_levy_jumpmark_nonpositive X
  have hterm : ∀ v : ℝ≥0,
      (if 0 < v ∧ v ≤ t then
        Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
      else 0) = 0 := by
    intro v
    split_ifs with hv
    · have ha := hn v hv.1 (hv.2.trans ht)
      have hb := hp ω v hv.1
      have heq : X.X v ω - Function.leftLim (fun z : ℝ≥0 => X.X z ω) v = 0 :=
        le_antisymm hb ha
      rw [sub_eq_zero.mp heq]
      ring
    · rfl
  simp only [hterm, tsum_zero]
