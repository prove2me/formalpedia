-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01b_lower_clock_eventually_closed_survival_of_mesh_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T11:47:56.202984+00:00
-- url     : https://prove2.me/submissions/16acfbd7-0d3c-463c-b5a6-5b9e48717329

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ws01b_lower_clock_strict_preclock_closed_survival

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Filter Topology Set
open scoped NNReal ENNReal

/-- An actual stopped mesh converging strictly before ruin eventually has a nonnegative complete past. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (ω : Ω) (t : ℝ≥0) (time : ℕ → ℝ≥0)
    (htend : Tendsto time atTop (𝓝 t))
    (hbefore : (t : ℝ≥0∞) < twoSidedExitDownTime X (-x) ω) :
    ∀ᶠ n in atTop, ∀ s : ℝ≥0, s ≤ time n → 0 ≤ x + X.X s ω := by
  have hcoe : Tendsto (fun n => (time n : ℝ≥0∞)) atTop
      (𝓝 (t : ℝ≥0∞)) :=
    ENNReal.continuous_coe.continuousAt.tendsto.comp htend
  have hevent : ∀ᶠ n in atTop,
      (time n : ℝ≥0∞) < twoSidedExitDownTime X (-x) ω :=
    hcoe.eventually (isOpen_Iio.mem_nhds hbefore)
  filter_upwards [hevent] with n hn
  exact avram_ws01b_lower_clock_strict_preclock_closed_survival
    X x ω (time n) hn
