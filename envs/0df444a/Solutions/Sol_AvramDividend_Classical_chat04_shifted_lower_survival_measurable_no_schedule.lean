-- Prove2me | solution 1 for AvramDividend.Classical.chat04_shifted_lower_survival_measurable_no_schedule
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T14:57:10.202721+00:00
-- url     : https://prove2.me/submissions/0cbd2e89-ffb3-497c-9c99-53dc686aa5d3

import Theorems.Thm_AvramDividend_Classical_chat04_lower_survival_closed_window_measurable
import Mathlib.Tactic.Linarith

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal

/-- Shifted-reserve nonruin on a closed horizon is measurable,
without any auxiliary rational-grid schedule. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (t : ℝ≥0) :
    MeasurableSet {ω | ∀ s : ℝ≥0,
      s ≤ t → 0 ≤ x + X.X s ω} := by
  have hBase := chat04_lower_survival_closed_window_measurable
    X (-x) 0 t (by exact zero_le)
  convert hBase using 1
  ext ω
  simp only [Set.mem_setOf_eq]
  constructor
  · intro h s hs0 hst
    have hh := h s hst
    linarith
  · intro h s hst
    have hh := h s (by exact zero_le) hst
    linarith