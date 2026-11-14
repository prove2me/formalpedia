-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB221_clipped_gradients_agree_off_nested_cutoff_strips
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T07:53:53.757224+00:00
-- url     : https://prove2.me/submissions/40aa12ba-c3ae-4e01-be9a-30c35e370747

import Mathlib.MeasureTheory.SetSemiring
import Mathlib.Analysis.Calculus.Deriv.Basic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
noncomputable section

/-- Clipped gradients differ only in nested boundary strips. -/
theorem solution
    (w : ℝ → ℝ) (a a' b' b B : ℝ)
    (ha : a ≤ a') (hab : a' ≤ b') (hb : b' ≤ b)
    (hB : 1 ≤ B)
    (hgrad : ∀ y ∈ Set.Icc a b, |deriv w y| ≤ B)
    (y : ℝ) :
    (y ∉ Set.Icc a a' → y ∉ Set.Icc b' b →
      (if y ∈ Set.Icc a b then deriv w y else 1) =
      (if y ∈ Set.Icc a' b' then deriv w y else 1)) ∧
    |(if y ∈ Set.Icc a b then deriv w y else 1) -
      (if y ∈ Set.Icc a' b' then deriv w y else 1)| ≤ 2 * B := by
  have hBoundWide :
      |if y ∈ Set.Icc a b then deriv w y else 1| ≤ B := by
    by_cases hy : y ∈ Set.Icc a b
    · simpa only [if_pos hy] using hgrad y hy
    · simpa only [if_neg hy, abs_one] using hB
  have hBoundNarrow :
      |if y ∈ Set.Icc a' b' then deriv w y else 1| ≤ B := by
    by_cases hy : y ∈ Set.Icc a' b'
    · have hyWide : y ∈ Set.Icc a b :=
        ⟨le_trans ha hy.1, le_trans hy.2 hb⟩
      simpa only [if_pos hy] using hgrad y hyWide
    · simpa only [if_neg hy, abs_one] using hB
  constructor
  · intro hleft hright
    have hmem : y ∈ Set.Icc a b ↔ y ∈ Set.Icc a' b' := by
      constructor
      · intro hy
        have hya : a' ≤ y := by
          by_contra hh
          exact hleft ⟨hy.1, le_of_lt (lt_of_not_ge hh)⟩
        have hyb : y ≤ b' := by
          by_contra hh
          exact hright ⟨le_of_lt (lt_of_not_ge hh), hy.2⟩
        exact ⟨hya, hyb⟩
      · intro hy
        exact ⟨le_trans ha hy.1, le_trans hy.2 hb⟩
    by_cases hy : y ∈ Set.Icc a b
    · simp only [if_pos hy, if_pos (hmem.mp hy)]
    · simp only [if_neg hy, if_neg (fun hh => hy (hmem.mpr hh))]
  · calc
      |(if y ∈ Set.Icc a b then deriv w y else 1) -
        (if y ∈ Set.Icc a' b' then deriv w y else 1)|
        = |(if y ∈ Set.Icc a b then deriv w y else 1) +
          -(if y ∈ Set.Icc a' b' then deriv w y else 1)| := by ring
      _ ≤ |if y ∈ Set.Icc a b then deriv w y else 1| +
          |-(if y ∈ Set.Icc a' b' then deriv w y else 1)| :=
            abs_add_le _ _
      _ = |if y ∈ Set.Icc a b then deriv w y else 1| +
          |if y ∈ Set.Icc a' b' then deriv w y else 1| := by rw [abs_neg]
      _ ≤ B + B := add_le_add hBoundWide hBoundNarrow
      _ = 2 * B := by ring

