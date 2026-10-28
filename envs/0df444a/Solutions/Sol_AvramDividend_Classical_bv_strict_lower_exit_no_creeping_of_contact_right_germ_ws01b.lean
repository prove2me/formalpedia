-- Prove2me | solution 1 for AvramDividend.Classical.bv_strict_lower_exit_no_creeping_of_contact_right_germ_ws01b
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T11:29:09.909075+00:00
-- url     : https://prove2.me/submissions/e0d2a77c-ae4d-4d8b-bf10-d7b3c682f492

import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_strictLowerCrossingClock_ne_contact_of_positiveRightGerm_ws01b
import Mathlib.Tactic
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal

/-- Conditional right positivity rules out strict lower-clock contact. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (a x : ℝ)
    (hGerm : ∀ᵐ ω ∂P,
      twoSidedExitDownTime X (-x) ω < twoSidedExitUpTime X (a - x) ω →
      x + X.X (twoSidedExitDownTime X (-x) ω).toNNReal ω = 0 →
      ∃ τ : ℝ≥0,
        (τ : ℝ≥0∞) = twoSidedExitDownTime X (-x) ω ∧
        ∃ ε : ℝ≥0, 0 < ε ∧
          ∀ t : ℝ≥0, τ < t → t < τ + ε → -x ≤ X.X t ω) :
    ∀ᵐ ω ∂P,
      twoSidedExitDownTime X (-x) ω < twoSidedExitUpTime X (a - x) ω →
      x + X.X (twoSidedExitDownTime X (-x) ω).toNNReal ω ≠ 0 := by
  filter_upwards [hGerm] with ω hω
  intro hFirst hZero
  obtain ⟨τ, hClock, ε, hε, hRight⟩ := hω hFirst hZero
  have hInf :
      (τ : ℝ≥0∞) =
        (⨅ (t : ℝ≥0) (_ : X.X t ω < -x), (t : ℝ≥0∞)) := by
    simpa [twoSidedExitDownTime] using hClock
  have hTo : (twoSidedExitDownTime X (-x) ω).toNNReal = τ := by
    rw [← hClock]
    simp
  have hContact : X.X τ ω = -x := by
    have hZero' : x + X.X τ ω = 0 := by
      simpa [hTo] using hZero
    linarith
  exact
    (strictLowerCrossingClock_ne_contact_of_positiveRightGerm_ws01b
      (fun t : ℝ≥0 => X.X t ω) (-x) τ hInf
      ⟨ε, hε, hRight⟩) hContact
