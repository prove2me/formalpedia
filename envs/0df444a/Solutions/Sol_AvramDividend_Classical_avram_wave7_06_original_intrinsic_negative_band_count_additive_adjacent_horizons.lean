-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_06_original_intrinsic_negative_band_count_additive_adjacent_horizons
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T14:27:20.306601+00:00
-- url     : https://prove2.me/submissions/dbd0fa30-0e91-442d-b9b3-8ef5c7d7ad1a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- Additivity of genuine source intrinsic marked counts on adjacent time intervals. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (T S : ℝ≥0) (n : ℕ) :
    (let NX : Measure (ℝ≥0 × ℝ) :=
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
     let B : Set ℝ := Iic (-(1 / ((n : ℝ) + 1)))
     NX (Ioc 0 (T + S) ×ˢ B) =
       NX (Ioc 0 T ×ˢ B) + NX (Ioc T (T + S) ×ˢ B)) := by
  classical
  let NX : Measure (ℝ≥0 × ℝ) :=
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
  let B : Set ℝ := Iic (-(1 / ((n : ℝ) + 1)))
  change NX (Ioc 0 (T + S) ×ˢ B) =
    NX (Ioc 0 T ×ˢ B) + NX (Ioc T (T + S) ×ˢ B)
  have hUnion :
      Ioc (0 : ℝ≥0) (T + S) ×ˢ B =
        (Ioc 0 T ×ˢ B) ∪ (Ioc T (T + S) ×ˢ B) := by
    ext p
    rcases p with ⟨t, z⟩
    simp only [mem_prod, mem_Ioc, mem_union]
    constructor
    · rintro ⟨⟨h0, hTS⟩, hz⟩
      by_cases hT : t ≤ T
      · exact Or.inl ⟨⟨h0, hT⟩, hz⟩
      · exact Or.inr ⟨⟨lt_of_not_ge hT, hTS⟩, hz⟩
    · rintro (⟨⟨h0, hT⟩, hz⟩ | ⟨⟨hT, hTS⟩, hz⟩)
      · exact ⟨⟨h0, hT.trans (le_add_of_nonneg_right (by positivity))⟩, hz⟩
      · exact ⟨⟨lt_of_le_of_lt (by positivity) hT, hTS⟩, hz⟩
  have hDisj :
      Disjoint (Ioc 0 T ×ˢ B) (Ioc T (T + S) ×ˢ B) := by
    apply Set.disjoint_left.mpr
    rintro p hpA hpB
    exact (not_lt_of_ge hpA.1.2) hpB.1.1
  have hMeas : MeasurableSet (Ioc T (T + S) ×ˢ B) := by
    exact measurableSet_Ioc.prod measurableSet_Iic
  rw [hUnion]
  exact measure_union hDisj hMeas
