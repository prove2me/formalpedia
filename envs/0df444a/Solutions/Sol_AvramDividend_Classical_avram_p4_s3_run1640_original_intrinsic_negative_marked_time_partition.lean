-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_s3_run1640_original_intrinsic_negative_marked_time_partition
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T17:12:03.332059+00:00
-- url     : https://prove2.me/submissions/38535410-4873-4d5f-a630-f75e639519c5

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Genuine original marked jumps split at every deterministic time, pathwise. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (s t : ℝ≥0) (hst : s ≤ t)
    (B : Set ℝ) (hB : MeasurableSet B) :
    let J : Set ℝ≥0 → ℝ≥0∞ := fun I =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (I ×ˢ B)
    J (Ioc 0 t) = J (Ioc 0 s) + J (Ioc s t) := by
  let μ : Measure (ℝ≥0 × ℝ) :=
    (Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))
  change μ (Ioc 0 t ×ˢ B) =
    μ (Ioc 0 s ×ˢ B) + μ (Ioc s t ×ˢ B)
  have hParts : (Ioc 0 s ×ˢ B) ∪ (Ioc s t ×ˢ B) =
      Ioc 0 t ×ˢ B := by
    ext q
    rcases q with ⟨u, z⟩
    simp only [Set.mem_union, Set.mem_prod, Set.mem_Ioc]
    constructor
    · rintro (⟨⟨h0u, hus⟩, hz⟩ | ⟨⟨hsu, hut⟩, hz⟩)
      · exact ⟨⟨h0u, hus.trans hst⟩, hz⟩
      · exact ⟨⟨lt_of_le_of_lt (show (0 : ℝ≥0) ≤ s from zero_le) hsu, hut⟩, hz⟩
    · rintro ⟨⟨h0u, hut⟩, hz⟩
      by_cases hus : u ≤ s
      · exact Or.inl ⟨⟨h0u, hus⟩, hz⟩
      · exact Or.inr ⟨⟨lt_of_not_ge hus, hut⟩, hz⟩
  have hDisj : Disjoint (Ioc 0 s ×ˢ B) (Ioc s t ×ˢ B) := by
    apply Set.disjoint_left.mpr
    intro q hA hC
    rcases q with ⟨u, z⟩
    simp only [Set.mem_prod, Set.mem_Ioc] at hA hC
    exact (not_lt_of_ge hA.1.2) hC.1.1
  have hMeas : MeasurableSet (Ioc s t ×ˢ B) :=
    measurableSet_Ioc.prod hB
  simpa only [hParts] using
    (measure_union hDisj hMeas :
      μ ((Ioc 0 s ×ˢ B) ∪ (Ioc s t ×ˢ B)) =
        μ (Ioc 0 s ×ˢ B) + μ (Ioc s t ×ˢ B))
