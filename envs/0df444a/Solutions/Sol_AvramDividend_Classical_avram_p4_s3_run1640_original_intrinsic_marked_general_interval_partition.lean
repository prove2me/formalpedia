-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_s3_run1640_original_intrinsic_marked_general_interval_partition
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T17:25:59.494493+00:00
-- url     : https://prove2.me/submissions/ff68e863-8416-4547-bf0e-8d4f9916e09a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Actual marked Lévy jumps add across every half-open subinterval partition. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (a s t : ℝ≥0) (has : a ≤ s) (hst : s ≤ t)
    (B : Set ℝ) (hB : MeasurableSet B) :
    let J : Set ℝ≥0 → ℝ≥0∞ := fun I =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (I ×ˢ B)
    J (Ioc a t) = J (Ioc a s) + J (Ioc s t) := by
  let μ : Measure (ℝ≥0 × ℝ) :=
    (Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))
  change μ (Ioc a t ×ˢ B) =
    μ (Ioc a s ×ˢ B) + μ (Ioc s t ×ˢ B)
  have hParts : (Ioc a s ×ˢ B) ∪ (Ioc s t ×ˢ B) =
      Ioc a t ×ˢ B := by
    ext q
    rcases q with ⟨u, z⟩
    simp only [Set.mem_union, Set.mem_prod, Set.mem_Ioc]
    constructor
    · rintro (⟨⟨hau, hus⟩, hz⟩ | ⟨⟨hsu, hut⟩, hz⟩)
      · exact ⟨⟨hau, hus.trans hst⟩, hz⟩
      · exact ⟨⟨lt_of_le_of_lt has hsu, hut⟩, hz⟩
    · rintro ⟨⟨hau, hut⟩, hz⟩
      by_cases hus : u ≤ s
      · exact Or.inl ⟨⟨hau, hus⟩, hz⟩
      · exact Or.inr ⟨⟨lt_of_not_ge hus, hut⟩, hz⟩
  have hDisj : Disjoint (Ioc a s ×ˢ B) (Ioc s t ×ˢ B) := by
    apply Set.disjoint_left.mpr
    intro q hA hC
    rcases q with ⟨u, z⟩
    simp only [Set.mem_prod, Set.mem_Ioc] at hA hC
    exact (not_lt_of_ge hA.1.2) hC.1.1
  have hMeas : MeasurableSet (Ioc s t ×ˢ B) :=
    measurableSet_Ioc.prod hB
  simpa only [hParts] using
    (measure_union hDisj hMeas :
      μ ((Ioc a s ×ˢ B) ∪ (Ioc s t ×ˢ B)) =
        μ (Ioc a s ×ˢ B) + μ (Ioc s t ×ˢ B))
