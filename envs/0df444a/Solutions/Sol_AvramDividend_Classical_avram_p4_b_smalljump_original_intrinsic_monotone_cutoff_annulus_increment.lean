-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_b_smalljump_original_intrinsic_monotone_cutoff_annulus_increment
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T23:22:10.713381+00:00
-- url     : https://prove2.me/submissions/b5e6b83c-04c8-47b6-aa2e-5c06408f6501

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_intrinsic_disjoint_mark_band_union_additive

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- The increment of the original marked count under an increasing cutoff
is exactly the count on the intervening disjoint mark annulus. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (B : ℕ → Set ℝ)
    (hMon : Monotone B) (hB : ∀ n, MeasurableSet (B n))
    (n : ℕ) (ω : Ω) :
    ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s t ×ˢ B (n + 1)) =
    ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s t ×ˢ B n) +
    ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s t ×ˢ (B (n + 1) \ B n)) := by
  have hSub : B n ⊆ B (n + 1) := hMon (Nat.le_succ n)
  have hDisj : Disjoint (B n) (B (n + 1) \ B n) := by
    apply Set.disjoint_left.mpr
    intro z hz hzDiff
    exact hzDiff.2 hz
  have hUnion : B n ∪ (B (n + 1) \ B n) = B (n + 1) := by
    ext z
    constructor
    · rintro (hz | ⟨hz, -⟩)
      · exact hSub hz
      · exact hz
    · intro hz
      by_cases hn : z ∈ B n
      · exact Or.inl hn
      · exact Or.inr ⟨hz, hn⟩
  simpa only [hUnion] using
    avram_p4_b_smalljump_original_intrinsic_disjoint_mark_band_union_additive
      X s t (B n) (B (n + 1) \ B n)
      (hB n) ((hB (n + 1)).diff (hB n)) hDisj ω
