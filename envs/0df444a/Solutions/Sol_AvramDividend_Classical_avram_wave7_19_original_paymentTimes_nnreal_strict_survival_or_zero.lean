-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_19_original_paymentTimes_nnreal_strict_survival_or_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T23:57:32.587569+00:00
-- url     : https://prove2.me/submissions/250db20c-546d-44f9-857c-d9dfa4ce3f34

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
/-- A zero payment time is allowed even when ruin occurs at zero;
positive payment times are strictly pre-ruin on the NNReal clock. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (ω : Ω) (t : ℝ)
    (ht : t ∈ paymentTimes (ruinTime X x D ω)) :
    t.toNNReal = 0 ∨
      (0 < t ∧ ((t.toNNReal : ℝ≥0∞) < ruinTime X x D ω)) := by
  change 0 ≤ t ∧ (t = 0 ∨ ENNReal.ofReal t < ruinTime X x D ω) at ht
  obtain ⟨htnonneg, hsurvive⟩ := ht
  by_cases hzero : t = 0
  · exact Or.inl (by simp [hzero])
  · have hpositive : 0 < t := by
      rcases lt_or_eq_of_le htnonneg with hp | heq
      · exact hp
      · exact False.elim (hzero heq.symm)
    rcases hsurvive with hz | hlt
    · exact False.elim (hzero hz)
    · right
      constructor
      · exact hpositive
      · change (t.toNNReal : ℝ≥0∞) < ruinTime X x D ω at hlt
        exact hlt
