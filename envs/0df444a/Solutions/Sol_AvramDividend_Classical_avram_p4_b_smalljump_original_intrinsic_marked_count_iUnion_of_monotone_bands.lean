-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_b_smalljump_original_intrinsic_marked_count_iUnion_of_monotone_bands
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T23:07:29.871828+00:00
-- url     : https://prove2.me/submissions/bd722617-48c2-491a-a7ec-c68d455f287c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- The actual original Lévy marked jump count is continuous from below
along increasing mark bands, on every fixed physical time rectangle. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (B : ℕ → Set ℝ) (hB : Monotone B) (ω : Ω) :
    ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s t ×ˢ (⋃ n, B n)) =
    ⨆ n, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s t ×ˢ B n) := by
  let N : Measure (ℝ≥0 × ℝ) :=
    (Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))
  have hMon : Monotone (fun n : ℕ => Ioc s t ×ˢ B n) := by
    intro i j hij
    rintro ⟨u, z⟩ ⟨hu, hz⟩
    exact ⟨hu, hB hij hz⟩
  have hUnion : Ioc s t ×ˢ (⋃ n, B n) =
      ⋃ n, Ioc s t ×ˢ B n := by
    ext ⟨u, z⟩
    simp only [mem_prod, mem_iUnion]
    constructor
    · rintro ⟨hu, ⟨n, hn⟩⟩
      exact ⟨n, ⟨hu, hn⟩⟩
    · rintro ⟨n, ⟨hu, hn⟩⟩
      exact ⟨hu, ⟨n, hn⟩⟩
  change N (Ioc s t ×ˢ (⋃ n, B n)) =
    ⨆ n, N (Ioc s t ×ˢ B n)
  rw [hUnion]
  exact hMon.measure_iUnion
