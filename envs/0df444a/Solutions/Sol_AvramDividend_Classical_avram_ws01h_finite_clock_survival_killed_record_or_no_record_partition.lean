-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01h_finite_clock_survival_killed_record_or_no_record_partition
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T10:42:20.141989+00:00
-- url     : https://prove2.me/submissions/e59a45b1-bfa6-41c1-bd71-cf7beafda1c5

import Mathlib
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_avram_ws01h_true_capped_record_full_survival_iff_lower_killed_fresh_future

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

/-- Exact finite-clock CDF event partition: killed first-record regeneration
or the no-record remainder, with the genuine source strict clocks. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x b : ℝ) (hb : 0 ≤ b)
    (N : ℝ≥0) (ω : Ω) (t : ℝ≥0) (htN : t ≤ N) :
    (let τ : ℝ≥0 :=
       (min (twoSidedExitUpTime X b ω) (N : ℝ≥0∞)).toNNReal
     (∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s ω) ↔
       (twoSidedExitUpTime X b ω < (t : ℝ≥0∞) ∧
        twoSidedExitUpTime X b ω <
          twoSidedExitDownTime X (-x) ω ∧
        ∀ u : ℝ≥0, u ≤ t - τ →
          0 ≤ (x + b) + (X.X (τ + u) ω - X.X τ ω)) ∨
       ((t : ℝ≥0∞) ≤ twoSidedExitUpTime X b ω ∧
         ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s ω)) := by
  intro τ
  by_cases hBefore : twoSidedExitUpTime X b ω < (t : ℝ≥0∞)
  · have hCap : twoSidedExitUpTime X b ω ≤ (N : ℝ≥0∞) :=
      hBefore.le.trans (ENNReal.coe_le_coe.mpr htN)
    have hSplit :
        (∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s ω) ↔
          (twoSidedExitUpTime X b ω <
             twoSidedExitDownTime X (-x) ω ∧
           ∀ u : ℝ≥0, u ≤ t - τ →
             0 ≤ (x + b) + (X.X (τ + u) ω - X.X τ ω)) := by
      simpa only [τ] using
        (avram_ws01h_true_capped_record_full_survival_iff_lower_killed_fresh_future
          X x b hb N ω t hCap hBefore)
    constructor
    · intro hSurvive
      exact Or.inl ⟨hBefore, hSplit.mp hSurvive⟩
    · rintro (h | h)
      · exact hSplit.mpr h.2
      · exact h.2
  · have hAfter : (t : ℝ≥0∞) ≤ twoSidedExitUpTime X b ω :=
      le_of_not_gt hBefore
    constructor
    · intro hSurvive
      exact Or.inr ⟨hAfter, hSurvive⟩
    · rintro (h | h)
      · exact False.elim (hBefore h.1)
      · exact h.2
