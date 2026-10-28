-- Prove2me | solution 1 for AvramDividend.Classical.reflected_infimum_integer_horizon_tendsto_inf
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T08:21:59.252803+00:00
-- url     : https://prove2.me/submissions/95b886fe-82db-4abb-8aee-0375b6500767

import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_killed_survival_capital_reflected_infimum_transform
import Theorems.Thm_AvramDividend_Classical_killed_survival_capital_antitone_horizon

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Integer-horizon reflected-infimum expectations tend to their infimum. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ : ℝ) (hθ : 0 < θ) :
    Tendsto (fun n : ℕ =>
      ∫⁻ (ω : Ω), ENNReal.ofReal (Real.exp (-θ * max 0
        (-sInf {y : ℝ | ∃ s : ℝ≥0, s ≤ (n : ℝ≥0) ∧
          y = X.X s ω})) / θ) ∂P) atTop
      (nhds (⨅ n : ℕ,
        ∫⁻ (ω : Ω), ENNReal.ofReal (Real.exp (-θ * max 0
          (-sInf {y : ℝ | ∃ s : ℝ≥0, s ≤ (n : ℝ≥0) ∧
            y = X.X s ω})) / θ) ∂P)) := by
  have ha : Antitone (fun n : ℕ =>
      ∫⁻ (ω : Ω), ENNReal.ofReal (Real.exp (-θ * max 0
        (-sInf {y : ℝ | ∃ s : ℝ≥0, s ≤ (n : ℝ≥0) ∧
          y = X.X s ω})) / θ) ∂P) := by
    intro n m hnm
    have htime : (n : ℝ≥0) ≤ (m : ℝ≥0) := by exact_mod_cast hnm
    change (∫⁻ (ω : Ω), ENNReal.ofReal (Real.exp (-θ * max 0
      (-sInf {y : ℝ | ∃ s : ℝ≥0, s ≤ (m : ℝ≥0) ∧ y = X.X s ω})) / θ) ∂P) ≤
      (∫⁻ (ω : Ω), ENNReal.ofReal (Real.exp (-θ * max 0
        (-sInf {y : ℝ | ∃ s : ℝ≥0, s ≤ (n : ℝ≥0) ∧ y = X.X s ω})) / θ) ∂P)
    rw [← killed_survival_capital_reflected_infimum_transform X (m : ℝ≥0) θ hθ,
        ← killed_survival_capital_reflected_infimum_transform X (n : ℝ≥0) θ hθ]
    exact killed_survival_capital_antitone_horizon X
      (n : ℝ≥0) (m : ℝ≥0) htime θ
  exact tendsto_atTop_iInf ha
