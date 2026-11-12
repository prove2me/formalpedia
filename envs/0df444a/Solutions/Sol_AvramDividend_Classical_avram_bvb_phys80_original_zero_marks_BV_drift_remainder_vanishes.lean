-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_phys80_original_zero_marks_BV_drift_remainder_vanishes
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T07:34:47.746202+00:00
-- url     : https://prove2.me/submissions/6b640bcd-9e53-457b-b91f-dc3ec338963d

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bvb_phys73_original_zero_negative_mark_count_no_negative_jumps
import Theorems.Thm_AvramDividend_Classical_avram_bvb_phys75_original_zero_negative_mark_count_entire_source_drift
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_levy_jumpmark_nonpositive
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Both the physical jump sum and the BV drift-remainder source vanish
at every time on the original event with zero negative marks. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (T : ℝ≥0) :
    ∀ᵐ ω ∂P,
      (((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω - Function.leftLim
          (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ Iio (0 : ℝ)) = 0) →
      ∀ t : ℝ≥0, t ≤ T →
        (let J : ℝ≥0 → ℝ := fun s =>
          ∑' v : ℝ≥0, if 0 < v ∧ v ≤ s then
            Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
          else 0
         ((t : ℝ) * X.drift - X.X t ω) - J t = 0) := by
  filter_upwards [avram_bvb_phys75_original_zero_negative_mark_count_entire_source_drift
    X hX hBV T] with ω hpath
  intro hZero t ht
  have hterm : ∀ v : ℝ≥0,
      (if 0 < v ∧ v ≤ t then
        Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
      else 0) = 0 := by
    intro v
    split_ifs with hv
    · have hnonneg := avram_bvb_phys73_original_zero_negative_mark_count_no_negative_jumps
        X ω T hZero v hv.1 (le_trans hv.2 ht)
      have hnonpos := avram_wave4_04a_actual_levy_jumpmark_nonpositive
        X ω v hv.1
      linarith
    · rfl
  have hJ : (∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
      Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
    else 0) = 0 := by
    simp only [hterm, tsum_zero]
  dsimp only
  rw [hJ, hpath hZero t ht]
  ring
