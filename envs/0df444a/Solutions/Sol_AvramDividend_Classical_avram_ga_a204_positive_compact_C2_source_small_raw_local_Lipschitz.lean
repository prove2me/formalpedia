-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a204_positive_compact_C2_source_small_raw_local_Lipschitz
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T23:56:28.800732+00:00
-- url     : https://prove2.me/submissions/ac20e065-9699-4a2f-a817-82d1c3b47954

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_ContDiffOn_compact_band_exists_lipschitz
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set AvramDividend.Classical
noncomputable section

/-- The original compact positive pre-stop reserve band gives a common local
Lipschitz constant for the true raw Gaussian spatial source increment. -/
theorem solution
    (w : ℝ → ℝ) (hw : ContDiffOn ℝ 2 w (Set.Ioi 0))
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    ∃ L : ℝ, 0 ≤ L ∧
      ∀ y ∈ Set.Icc a b, ∀ r : ℝ, |r| < a / 2 →
      |w (y + r) - w y| ≤ L * |r| := by
  let lo : ℝ := a / 2
  let hi : ℝ := b + a / 2
  have hlo : 0 < lo := by dsimp [lo]; linarith
  have hSub : Set.Icc lo hi ⊆ Set.Ioi (0 : ℝ) := by
    intro z hz
    exact lt_of_lt_of_le hlo hz.1
  have hw1 : ContDiffOn ℝ 1 w (Set.Ioi 0) :=
    hw.of_le (by norm_num)
  obtain ⟨L,hL,hLip⟩ :=
    avram_p3_2_original_ContDiffOn_compact_band_exists_lipschitz
      w (Set.Ioi 0) hw1 lo hi hSub
  refine ⟨L,hL,?_⟩
  intro y hy r hr
  have hyl : lo ≤ y := by
    dsimp [lo]
    linarith [hy.1]
  have hyu : y ≤ hi := by
    dsimp [hi]
    linarith [hy.2]
  have hrPair : -(a / 2) < r ∧ r < a / 2 := abs_lt.mp hr
  have hpos : lo ≤ y + r := by
    dsimp [lo]
    linarith [hy.1, hrPair.1]
  have hupper : y + r ≤ hi := by
    dsimp [hi]
    linarith [hy.2, hrPair.2]
  have hBound := hLip (y + r) ⟨hpos,hupper⟩ y ⟨hyl,hyu⟩
  convert hBound using 1 <;> ring
