-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01h_true_capped_record_full_survival_iff_lower_killed_fresh_future
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T10:39:06.79113+00:00
-- url     : https://prove2.me/submissions/0eaf6ed9-c052-46d8-9865-3baacc786569

import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_avram_ws01h_finite_survival_earlier_record_before_ruin
import Theorems.Thm_AvramDividend_Classical_avram_ws01h_upper_first_preserves_lower_survival_through_record
import Theorems.Thm_AvramDividend_Classical_avram_ws01h_deterministic_closed_survival_at_record_split
import Theorems.Thm_AvramDividend_Classical_avram_ws01h_capped_record_no_positive_overshoot
import Theorems.Thm_AvramDividend_Classical_firstRecord_capped_clock_eq_uncapped_of_le_horizon

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

/-- On a genuine capped upper record strictly before the observation horizon,
closed survival equals lower-killed history followed by survival of the exact
shifted post-record process from the attained upper reserve. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x b : ℝ) (hb : 0 ≤ b)
    (N : ℝ≥0) (ω : Ω) (t : ℝ≥0)
    (hCap : twoSidedExitUpTime X b ω ≤ (N : ℝ≥0∞))
    (hEarlier : twoSidedExitUpTime X b ω < (t : ℝ≥0∞)) :
    (let τ : ℝ≥0 :=
       (min (twoSidedExitUpTime X b ω) (N : ℝ≥0∞)).toNNReal
     (∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s ω) ↔
       twoSidedExitUpTime X b ω <
         twoSidedExitDownTime X (-x) ω ∧
       ∀ u : ℝ≥0, u ≤ t - τ →
         0 ≤ (x + b) + (X.X (τ + u) ω - X.X τ ω)) := by
  intro τ
  have hClock : (τ : ℝ≥0∞) = twoSidedExitUpTime X b ω := by
    exact firstRecord_capped_clock_eq_uncapped_of_le_horizon X b N ω hCap
  have hτt : τ ≤ t := ENNReal.coe_le_coe.mp
    ((hClock.trans_lt hEarlier).le)
  have hStop : X.X τ ω = b :=
    avram_ws01h_capped_record_no_positive_overshoot X b hb N ω hCap
  have hSplit :=
    avram_ws01h_deterministic_closed_survival_at_record_split
      (fun s : ℝ≥0 => X.X s ω) x τ t hτt
  constructor
  · intro hFull
    have hKill : twoSidedExitUpTime X b ω <
        twoSidedExitDownTime X (-x) ω :=
      avram_ws01h_finite_survival_earlier_record_before_ruin
        X x b ω t hEarlier hFull
    have hFuture := hSplit.mp hFull |>.2
    refine ⟨hKill, ?_⟩
    simpa only [hStop] using hFuture
  · rintro ⟨hKill, hFuture⟩
    apply hSplit.mpr
    constructor
    · intro s hs
      apply avram_ws01h_upper_first_preserves_lower_survival_through_record
        X x b ω s hKill
      rw [← hClock]
      exact ENNReal.coe_le_coe.mpr hs
    · simpa only [hStop] using hFuture
