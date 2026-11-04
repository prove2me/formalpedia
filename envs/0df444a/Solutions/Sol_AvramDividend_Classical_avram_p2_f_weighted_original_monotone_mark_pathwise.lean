-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_f_weighted_original_monotone_mark_pathwise
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T17:16:08.254773+00:00
-- url     : https://prove2.me/submissions/203d22fe-ef34-4d14-83ca-569e0a0e6b8b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- Genuine original intrinsic marked counts are continuous from below
on any monotone sequence of mark bands, with infinite counts allowed. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s T : ℝ≥0) (B : ℕ → Set ℝ)
    (hMono : Monotone B) :
    ∀ ω, ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s (s + T) ×ˢ (⋃ n, B n)) =
      ⨆ n, ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s (s + T) ×ˢ (B n)) := by
  intro ω
  have hSet : Ioc s (s + T) ×ˢ (⋃ n, B n) =
      ⋃ n, Ioc s (s + T) ×ˢ B n := by
    ext p
    simp only [Set.mem_prod, Set.mem_iUnion]
    constructor
    · rintro ⟨ht, n, hn⟩
      exact ⟨n, ht, hn⟩
    · rintro ⟨n, ht, hn⟩
      exact ⟨ht, n, hn⟩
  have hRect : Monotone
      (fun n => Ioc s (s + T) ×ˢ B n) := by
    intro i j hij
    exact Set.prod_mono Subset.rfl (hMono hij)
  rw [hSet]
  exact hRect.measure_iUnion
