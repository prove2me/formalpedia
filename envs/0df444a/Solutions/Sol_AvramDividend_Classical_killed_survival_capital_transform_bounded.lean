-- Prove2me | solution 1 for AvramDividend.Classical.killed_survival_capital_transform_bounded
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T08:04:30.889119+00:00
-- url     : https://prove2.me/submissions/4f50b912-a00e-4981-8951-f4d7db2522ea

import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Theorems.Thm_AvramDividend_Classical_killed_survival_capital_reflected_infimum_transform

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- The finite-horizon killed-survival capital Laplace mass is at most 1 / θ. -/
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
        (x, ω) ∂P ∂volume) ≤ ENNReal.ofReal (1 / θ) := by
  letI : IsProbabilityMeasure P := X.isProbability
  rw [killed_survival_capital_reflected_infimum_transform X t θ hθ]
  have hp (ω : Ω) :
      ENNReal.ofReal (Real.exp (-θ * max 0
        (-sInf {y : ℝ | ∃ s : ℝ≥0, s ≤ t ∧ y = X.X s ω})) / θ) ≤
        ENNReal.ofReal (1 / θ) := by
    apply ENNReal.ofReal_le_ofReal
    have hnonpos : -θ * max 0
        (-sInf {y : ℝ | ∃ s : ℝ≥0, s ≤ t ∧ y = X.X s ω}) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg
        (neg_nonpos.mpr hθ.le) (le_max_left _ _)
    exact div_le_div_of_nonneg_right
      (Real.exp_le_one_iff.mpr hnonpos) hθ.le
  calc
    (∫⁻ (ω : Ω), ENNReal.ofReal (Real.exp (-θ * max 0
        (-sInf {y : ℝ | ∃ s : ℝ≥0, s ≤ t ∧ y = X.X s ω})) / θ) ∂P) ≤
      (∫⁻ (_ : Ω), ENNReal.ofReal (1 / θ) ∂P) :=
        lintegral_mono hp
    _ = ENNReal.ofReal (1 / θ) := by simp
