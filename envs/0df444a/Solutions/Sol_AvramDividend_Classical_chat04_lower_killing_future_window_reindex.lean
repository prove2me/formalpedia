-- Prove2me | solution 1 for AvramDividend.Classical.chat04_lower_killing_future_window_reindex
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T20:59:50.803993+00:00
-- url     : https://prove2.me/submissions/8c2415f1-5b48-44fb-8c5f-cba7a836c347

import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Positivity
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal
open AvramDividend.Classical

/-! Re-index one-sided future ruin survival onto elapsed Levy time.
The two endpoints of the observation window are preserved exactly. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (s u : ℝ≥0) (hsu : s ≤ u) :
    {ω | ∀ v : ℝ≥0, s ≤ v → v ≤ u →
      0 ≤ (x + X.X s ω) + (X.X v ω - X.X s ω)} =
      {ω | ∀ r : ℝ≥0, r ≤ u - s →
        0 ≤ (x + X.X s ω) + (X.X (s + r) ω - X.X s ω)} := by
  ext ω
  simp only [Set.mem_setOf_eq]
  constructor
  · intro h r hr
    have hlow : s ≤ s + r := le_add_of_nonneg_right (by positivity)
    have hhigh : s + r ≤ u := by
      calc
        s + r ≤ s + (u - s) := by gcongr
        _ = u := add_tsub_cancel_of_le hsu
    exact h (s + r) hlow hhigh
  · intro h v hsv hvu
    have hdiff : v - s ≤ u - s := tsub_le_tsub_right hvu s
    have heq : s + (v - s) = v := add_tsub_cancel_of_le hsv
    simpa only [heq] using h (v - s) hdiff
