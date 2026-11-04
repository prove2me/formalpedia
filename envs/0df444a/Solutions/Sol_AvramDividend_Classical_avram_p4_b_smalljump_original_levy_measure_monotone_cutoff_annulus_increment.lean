-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_b_smalljump_original_levy_measure_monotone_cutoff_annulus_increment
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T23:58:11.866983+00:00
-- url     : https://prove2.me/submissions/b5f07ceb-2f6d-4b9a-90ae-e9565f26cfe9

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- The original Lévy intensity increment along increasing Borel mark
cutoffs is the original intensity of the intervening disjoint annulus. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (B : ℕ → Set ℝ) (hMon : Monotone B)
    (hB : ∀ n, MeasurableSet (B n)) (n : ℕ) :
    X.ν (B (n + 1)) =
      X.ν (B n) + X.ν (B (n + 1) \ B n) := by
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
  conv_lhs => rw [← hUnion]
  exact measure_union hDisj ((hB (n + 1)).diff (hB n))
