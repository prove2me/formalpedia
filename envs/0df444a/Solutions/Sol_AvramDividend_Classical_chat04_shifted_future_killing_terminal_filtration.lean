-- Prove2me | solution 1 for AvramDividend.Classical.chat04_shifted_future_killing_terminal_filtration
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T22:16:02.687098+00:00
-- url     : https://prove2.me/submissions/f3fbaf7b-51a1-46ac-9ef7-677669cf861d

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat04_lower_survival_closed_window_filtration_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal
open AvramDividend.Classical

/-! The shifted future-interval killing event used by the killed-scale
conditional expectation is observable at the terminal time. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (s u : ℝ≥0) (hsu : s ≤ u) :
    MeasurableSet[𝓕 u]
      {ω | ∀ v : ℝ≥0, s ≤ v → v ≤ u →
        0 ≤ (x + X.X s ω) + (X.X v ω - X.X s ω)} := by
  have hEq :
      {ω | ∀ v : ℝ≥0, s ≤ v → v ≤ u →
        0 ≤ (x + X.X s ω) + (X.X v ω - X.X s ω)} =
      {ω | ∀ v : ℝ≥0, s ≤ v → v ≤ u →
        ¬ X.X v ω < -x} := by
    ext ω
    simp only [Set.mem_setOf_eq]
    constructor
    · intro h v hsv hvu
      have h0 := h v hsv hvu
      have heq :
          (x + X.X s ω) + (X.X v ω - X.X s ω) =
            x + X.X v ω := by ring
      rw [heq] at h0
      linarith
    · intro h v hsv hvu
      have h0 := h v hsv hvu
      have heq :
          (x + X.X s ω) + (X.X v ω - X.X s ω) =
            x + X.X v ω := by ring
      rw [heq]
      linarith
  rw [hEq]
  exact chat04_lower_survival_closed_window_filtration_measurable
    X (-x) s u hsu
