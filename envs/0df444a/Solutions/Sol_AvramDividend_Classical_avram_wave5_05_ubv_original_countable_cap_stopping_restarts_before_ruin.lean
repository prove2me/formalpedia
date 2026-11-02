-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_05_ubv_original_countable_cap_stopping_restarts_before_ruin
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T10:34:21.375233+00:00
-- url     : https://prove2.me/submissions/3dc54ab6-6aec-436a-b4e6-4ace836608bf

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.MeasureTheory.OuterMeasure.AE
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_05_ubv_original_surviving_cap_stopping_enters_strict_subcap_immediately

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-!
An Ito localization can restart at countably many cap-contact stopping times.
The original source controls all such restarts on a single probability-one event;
there is no terminal stopping at the first cap contact.
-/

/-- Countably simultaneous original-source cap restarts before ruin. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (x c : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (τ : ℕ → Ω → ℝ≥0)
    (hτ : ∀ n (s : ℝ≥0),
      MeasurableSet[𝓕 s] {ω : Ω | τ n ω ≤ s})
    (hstop : ∀ n, IsStoppingTime 𝓕
      (fun ω => (τ n ω : WithTop ℝ≥0))) :
    ∀ᵐ ω ∂P, ∀ n : ℕ,
      (τ n ω : ℝ≥0∞) < ruinTime X x D ω →
      riskProcess X x D (τ n ω) ω = c →
      ∀ ε : ℝ≥0, 0 < ε →
        ∃ s : ℝ≥0, 0 < s ∧ s < ε ∧
          ((τ n ω + s : ℝ≥0) : ℝ≥0∞) < ruinTime X x D ω ∧
          riskProcess X x D (τ n ω + s) ω < c := by
  apply (ae_all_iff).2
  intro n
  exact
    avram_wave5_05_ubv_original_surviving_cap_stopping_enters_strict_subcap_immediately
      X hBV x c D hD (τ n) (hτ n) (hstop n)
