-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_01_bv_original_future_negative_mark_interval_exact_rate
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T22:17:38.897593+00:00
-- url     : https://prove2.me/submissions/10391319-62f5-4b2b-a481-6fc8a718d75d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_01_bv_original_future_fullmark_expected_count_exact_gap_rate
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_intrinsic_jump_measure_negative_support
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (s t : ℝ≥0) (hs : 0 < s) (hst : s ≤ t) :
    (∫⁻ ω, ((Measure.count.restrict {v : ℝ≥0 |
      0 < v ∧ X.X v ω -
        Function.leftLim (fun w : ℝ≥0 => X.X w ω) v ≠ 0}).map
      (fun v : ℝ≥0 => (v, X.X v ω -
        Function.leftLim (fun w : ℝ≥0 => X.X w ω) v)))
      (Ioc s t ×ˢ Iio (0 : ℝ)) ∂P) =
      ((t - s : ℝ≥0) : ℝ≥0∞) * X.ν (Iio (0 : ℝ)) := by
  classical
  let N : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
    ((Measure.count.restrict {v : ℝ≥0 |
      0 < v ∧ X.X v ω -
        Function.leftLim (fun w : ℝ≥0 => X.X w ω) v ≠ 0}).map
      (fun v : ℝ≥0 => (v, X.X v ω -
        Function.leftLim (fun w : ℝ≥0 => X.X w ω) v)))
  have hPoint (ω : Ω) :
      N ω (Ioc s t ×ˢ Iio (0 : ℝ)) =
        N ω (Ioc s t ×ˢ (Set.univ : Set ℝ)) := by
    have hNeg :
        N ω (Ioc s t ×ˢ Ici (0 : ℝ)) = 0 :=
      avram_wave4_04a_actual_intrinsic_jump_measure_negative_support
        X ω s t
    have hCover :
        (Ioc s t ×ˢ Iio (0 : ℝ)) ∪
        (Ioc s t ×ˢ Ici (0 : ℝ)) =
        Ioc s t ×ˢ (Set.univ : Set ℝ) := by
      ext p
      simp only [mem_union, mem_prod, mem_Iio, mem_Ici, mem_univ,
        and_true]
      constructor
      · rintro (⟨hu, hy⟩ | ⟨hu, hy⟩)
        · exact hu
        · exact hu
      · intro hu
        rcases lt_or_ge p.2 (0 : ℝ) with hy | hy
        · exact Or.inl ⟨hu, hy⟩
        · exact Or.inr ⟨hu, hy⟩
    have hDisj :
        Disjoint (Ioc s t ×ˢ Iio (0 : ℝ))
          (Ioc s t ×ˢ Ici (0 : ℝ)) := by
      apply Set.disjoint_left.mpr
      rintro ⟨u, y⟩ ⟨_, hy⟩ ⟨_, hy'⟩
      change y < (0 : ℝ) at hy
      change (0 : ℝ) ≤ y at hy'
      exact (not_lt_of_ge hy') hy
    have hUnion :=
      measure_union hDisj (measurableSet_Ioc.prod measurableSet_Ici)
        (μ := N ω)
    rw [hCover, hNeg] at hUnion
    simpa using hUnion.symm
  change (∫⁻ ω, N ω (Ioc s t ×ˢ Iio (0 : ℝ)) ∂P) =
    ((t - s : ℝ≥0) : ℝ≥0∞) * X.ν (Iio (0 : ℝ))
  calc
    (∫⁻ ω, N ω (Ioc s t ×ˢ Iio (0 : ℝ)) ∂P) =
        ∫⁻ ω, N ω (Ioc s t ×ˢ (Set.univ : Set ℝ)) ∂P := by
      apply lintegral_congr
      intro ω
      exact hPoint ω
    _ = _ := avram_wave6_01_bv_original_future_fullmark_expected_count_exact_gap_rate
      X hBV hFinite s t hs hst
