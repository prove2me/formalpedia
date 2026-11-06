-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_s3_original_marked_negative_borel_cell_dominated_by_full_band
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T10:17:25.973078+00:00
-- url     : https://prove2.me/submissions/639db834-38f1-4745-b540-9086b054ab69

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_count_eq_finite_marked_time_card

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Any marked negative cell is bounded by its physical full-band count. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (n : ℕ)
    (s t : ℝ≥0) (hst : s ≤ t) (htT : t ≤ T)
    (B : Set ℝ)
    (hBsep : B ⊆ Iic (-(1 / ((n : ℝ) + 1)))) :
    ∀ ω : Ω,
      (((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B)).toReal ≤
      ({u : ℝ≥0 | 0 < u ∧ u ≤ T ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
          -(1 / ((n : ℝ) + 1))}.ncard : ℝ) := by
  intro ω
  let NX : Measure (ℝ≥0 × ℝ) :=
    (Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))
  let K : ℕ := {u : ℝ≥0 | 0 < u ∧ u ≤ T ∧
    X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
      -(1 / ((n : ℝ) + 1))}.ncard
  change (NX (Ioc s t ×ˢ B)).toReal ≤ (K : ℝ)
  have hSub : Ioc s t ×ˢ B ⊆
      Ioc 0 T ×ˢ Iic (-(1 / ((n : ℝ) + 1))) := by
    rintro ⟨u, z⟩ ⟨hu, hz⟩
    exact ⟨⟨lt_of_le_of_lt (show (0 : ℝ≥0) ≤ s from zero_le) hu.1, hu.2.trans htT⟩, hBsep hz⟩
  have hMono : NX (Ioc s t ×ˢ B) ≤
      NX (Ioc 0 T ×ˢ Iic (-(1 / ((n : ℝ) + 1)))) :=
    measure_mono hSub
  have hFull : NX (Ioc 0 T ×ˢ Iic (-(1 / ((n : ℝ) + 1)))) =
      (K : ℝ≥0∞) :=
    avram_wave7_06_original_negative_band_count_eq_finite_marked_time_card
      X ω T n
  rw [hFull] at hMono
  have hReal := ENNReal.toReal_mono (by simp) hMono
  simpa only [ENNReal.toReal_natCast] using hReal
