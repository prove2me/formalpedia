-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_b_smalljump_original_intrinsic_disjoint_mark_band_union_additive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T23:07:23.130747+00:00
-- url     : https://prove2.me/submissions/8f1d7154-e107-402a-a57b-cd59f64199b9

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- For the actual original Lévy intrinsic marked jump measure, counts on
two disjoint Borel mark bands add on a fixed physical time rectangle. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (B C : Set ℝ)
    (hB : MeasurableSet B) (hC : MeasurableSet C)
    (hBC : Disjoint B C) (ω : Ω) :
    ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s t ×ˢ (B ∪ C)) =
    ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s t ×ˢ B) +
    ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s t ×ˢ C) := by
  let N : Measure (ℝ≥0 × ℝ) :=
    (Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))
  have hUnion : Ioc s t ×ˢ (B ∪ C) =
      (Ioc s t ×ˢ B) ∪ (Ioc s t ×ˢ C) := by
    ext ⟨u, z⟩
    simp [and_or_left]
  have hd : Disjoint (Ioc s t ×ˢ B) (Ioc s t ×ˢ C) := by
    apply Set.disjoint_left.mpr
    rintro ⟨u, z⟩ h₁ h₂
    exact Set.disjoint_left.mp hBC h₁.2 h₂.2
  have hc : MeasurableSet (Ioc s t ×ˢ C) :=
    measurableSet_Ioc.prod hC
  change N (Ioc s t ×ˢ (B ∪ C)) =
    N (Ioc s t ×ˢ B) + N (Ioc s t ×ˢ C)
  rw [hUnion, measure_union hd hc]
