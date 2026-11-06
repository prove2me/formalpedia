-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_env3_turn9_original_stopped_physical_grid_times_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T21:56:17.070735+00:00
-- url     : https://prove2.me/submissions/37254523-b3f5-46bb-8fd4-e6d642b8dad3

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_ruinTime_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Every finitely stopped physical-grid clock is measurable and remains
inside the original dividend strategy's ruin-stopped horizon. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (T : ℝ≥0) (m : ℕ) :
    let τ : Ω → ℝ≥0 := fun ω =>
      (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
    let u : ℕ → Ω → ℝ≥0 := fun j ω =>
      min (((min j (m + 1) : ℕ) : ℝ≥0) *
        (T / (m + 1))) (τ ω)
    (∀ j, Measurable (u j)) ∧ (∀ j ω, u j ω ≤ τ ω) := by
  dsimp
  have hτ : Measurable (fun ω : Ω =>
      (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal) := by
    exact ENNReal.measurable_toNNReal.comp
      ((ruinTime_measurable X x D hD.1.1).min measurable_const)
  constructor
  · intro j
    exact measurable_const.min hτ
  · intro j ω
    exact min_le_right _ _
