-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_phys72_original_zero_negative_mark_count_excludes_each_band
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T00:37:00.302501+00:00
-- url     : https://prove2.me/submissions/3a7524f1-5e8f-4691-bd12-85ffecc7a06c

import Mathlib.Probability.Process.Filtration
import Theorems.Thm_AvramDividend_Classical_avram_bv_zero13_original_negative_band_count_real_positive_iff_exists_jump
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Zero original negative marked count excludes each annulus of negative
jump sizes, by monotonicity of the exact marked measure. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (T : ℝ≥0) (n : ℕ)
    (hZero : ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u) ≠ 0}).map
      (fun u : ℝ≥0 => (u, (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))))
      (Ioc 0 T ×ˢ Iio (0 : ℝ)) = 0) :
    ¬ ∃ u : ℝ≥0, 0 < u ∧ u ≤ T ∧
      (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u) ≤ -(1 / ((n : ℝ) + 1)) := by
  let μ : Measure (ℝ≥0 × ℝ) := ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u) ≠ 0}).map
      (fun u : ℝ≥0 => (u, (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))))
  have hc : -(1 / ((n : ℝ) + 1)) < 0 := by
    have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := one_div_pos.mpr hn
    linarith
  have hsub :
      Ioc (0 : ℝ≥0) T ×ˢ Iic (-(1 / ((n : ℝ) + 1))) ⊆
        Ioc (0 : ℝ≥0) T ×ˢ Iio (0 : ℝ) := by
    intro p hp
    exact ⟨hp.1, lt_of_le_of_lt hp.2 hc⟩
  have hZeroBand :
      μ (Ioc (0 : ℝ≥0) T ×ˢ Iic (-(1 / ((n : ℝ) + 1)))) = 0 := by
    exact le_antisymm ((measure_mono hsub).trans_eq hZero) zero_le
  intro hex
  have hh := (avram_bv_zero13_original_negative_band_count_real_positive_iff_exists_jump
    X ω T n).mpr hex
  change 0 < (μ (Ioc (0 : ℝ≥0) T ×ˢ Iic (-(1 / ((n : ℝ) + 1))))).toReal at hh
  rw [hZeroBand] at hh
  norm_num at hh
