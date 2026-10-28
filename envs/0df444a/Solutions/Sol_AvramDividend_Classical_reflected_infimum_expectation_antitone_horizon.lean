-- Prove2me | solution 1 for AvramDividend.Classical.reflected_infimum_expectation_antitone_horizon
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T08:21:17.459823+00:00
-- url     : https://prove2.me/submissions/11adb82b-db00-4390-af92-bffe2873d4fe

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_killed_survival_capital_reflected_infimum_transform
import Theorems.Thm_AvramDividend_Classical_killed_survival_capital_antitone_horizon

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- The expected reflected-running-infimum envelope decreases with the horizon. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (t u : ℝ≥0) (htu : t ≤ u) (θ : ℝ) (hθ : 0 < θ) :
    (∫⁻ (ω : Ω),
      ENNReal.ofReal (Real.exp (-θ * max 0
        (-sInf {y : ℝ | ∃ s : ℝ≥0, s ≤ u ∧ y = X.X s ω})) / θ) ∂P) ≤
    (∫⁻ (ω : Ω),
      ENNReal.ofReal (Real.exp (-θ * max 0
        (-sInf {y : ℝ | ∃ s : ℝ≥0, s ≤ t ∧ y = X.X s ω})) / θ) ∂P) := by
  rw [← killed_survival_capital_reflected_infimum_transform X u θ hθ,
      ← killed_survival_capital_reflected_infimum_transform X t θ hθ]
  exact killed_survival_capital_antitone_horizon X t u htu θ
