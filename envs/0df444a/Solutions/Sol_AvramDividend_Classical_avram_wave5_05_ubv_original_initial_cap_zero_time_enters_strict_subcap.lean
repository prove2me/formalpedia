-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_05_ubv_original_initial_cap_zero_time_enters_strict_subcap
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T11:56:13.890485+00:00
-- url     : https://prove2.me/submissions/9a776036-de51-4676-899d-27546581de93

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_05_ubv_original_surviving_cap_stopping_enters_strict_subcap_immediately

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-!
Initial reserve at the cap is allowed. The controlled UBV path enters
strictly below cap immediately before ruin. This is the time-zero
specialisation of the already Proved genuine stopping-time boundary.
-/

/-- Actual surviving source reserve escapes any cap at initial time zero. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (x c : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D) :
    ∀ᵐ ω ∂P,
      (0 : ℝ≥0∞) < ruinTime X x D ω →
      riskProcess X x D 0 ω = c →
      ∀ ε : ℝ≥0, 0 < ε →
        ∃ s : ℝ≥0, 0 < s ∧ s < ε ∧
          (s : ℝ≥0∞) < ruinTime X x D ω ∧
          riskProcess X x D s ω < c := by
  have hτ : ∀ s : ℝ≥0,
      MeasurableSet[𝓕 s] {ω : Ω | (0 : ℝ≥0) ≤ s} := by
    intro s
    simp
  have hStop : IsStoppingTime 𝓕
      (fun _ : Ω => (0 : WithTop ℝ≥0)) := by
    intro s
    simp
  have hBase :=
    avram_wave5_05_ubv_original_surviving_cap_stopping_enters_strict_subcap_immediately
      X hBV x c D hD (fun _ : Ω => (0 : ℝ≥0)) hτ hStop
  simpa using hBase
