-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_mixed12_original_finite_activity_all_nonzero_marks_locally_finite_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-08T17:10:23.224233+00:00
-- url     : https://prove2.me/submissions/c8a3e6e5-5cae-4551-8d6b-d019606022c8

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_mixed12_original_finite_activity_negative_counts_all_bounded_ae
import Theorems.Thm_AvramDividend_Classical_avram_bv_jump8_original_frozen_mark_maps_measurable
import Theorems.Thm_AvramDividend_Classical_avram_p2_c_borel_original_no_nonnegative_mark_counts

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 t ×ˢ (Set.univ : Set ℝ)) < ⊤ := by
  let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
  have hNeg := avram_ubv_mixed12_original_finite_activity_negative_counts_all_bounded_ae
    X hFinite
  filter_upwards [hNeg] with ω hω
  intro t
  have hMarkMeas : Measurable (fun u : ℝ≥0 => (u,
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)) :=
    (avram_bv_jump8_original_frozen_mark_maps_measurable X ω 0).1
  have hPos : NX ω (Ioc 0 t ×ˢ Ici (0 : ℝ)) = 0 := by
    simpa only [NX] using
      avram_p2_c_borel_original_no_nonnegative_mark_counts
        X ω 0 t (Ici (0 : ℝ)) measurableSet_Ici (Subset.rfl) hMarkMeas
  have hCover : Ioc (0 : ℝ≥0) t ×ˢ (Set.univ : Set ℝ) ⊆
      (Ioc 0 t ×ˢ Iio (0 : ℝ)) ∪ (Ioc 0 t ×ˢ Ici (0 : ℝ)) := by
    rintro ⟨u, z⟩ ⟨hu, -⟩
    by_cases hz : z < 0
    · exact Or.inl ⟨hu, hz⟩
    · exact Or.inr ⟨hu, le_of_not_gt hz⟩
  have hBound : NX ω (Ioc 0 t ×ˢ (Set.univ : Set ℝ)) ≤
      NX ω (Ioc 0 t ×ˢ Iio (0 : ℝ)) +
        NX ω (Ioc 0 t ×ˢ Ici (0 : ℝ)) :=
    (measure_mono hCover).trans (measure_union_le _ _)
  rw [hPos, add_zero] at hBound
  exact lt_of_le_of_lt hBound (hω t)
