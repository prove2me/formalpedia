-- Prove2me | solution 1 for AvramDividend.Classical.killed_survival_real_expectation_bridge
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T08:00:07.970464+00:00
-- url     : https://prove2.me/submissions/71c51f67-6109-4411-8355-c64c704fe049

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Theorems.Thm_AvramDividend_Classical_killed_survival_capital_reflected_infimum_transform
import Theorems.Thm_AvramDividend_Classical_reflected_infimum_envelope_integrable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- The nonnegative killed-survival resolvent equals a finite real expectation. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (t : ℝ≥0) (θ : ℝ) (hθ : 0 < θ) :
    (∫⁻ (x : ℝ), ∫⁻ (ω : Ω),
      Set.indicator
        {p : ℝ × Ω | 0 < p.1 ∧
          ∀ s : ℝ≥0, s ≤ t → 0 ≤ p.1 + X.X s p.2}
        (fun p => ENNReal.ofReal (Real.exp (-θ * p.1)))
        (x, ω) ∂P ∂volume) =
    ENNReal.ofReal (∫ (ω : Ω),
      Real.exp (-θ * max 0
        (-sInf {y : ℝ | ∃ s : ℝ≥0, s ≤ t ∧ y = X.X s ω})) / θ ∂P) := by
  rw [killed_survival_capital_reflected_infimum_transform X t θ hθ]
  exact (ofReal_integral_eq_lintegral_ofReal
    (reflected_infimum_envelope_integrable X t θ hθ)
    (Filter.Eventually.of_forall (fun ω =>
      div_nonneg (Real.exp_nonneg _) hθ.le))).symm
