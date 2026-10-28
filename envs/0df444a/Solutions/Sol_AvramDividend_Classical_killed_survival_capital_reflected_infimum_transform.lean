-- Prove2me | solution 1 for AvramDividend.Classical.killed_survival_capital_reflected_infimum_transform
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T07:56:43.628176+00:00
-- url     : https://prove2.me/submissions/c41509f6-df2e-45b0-9494-9d599c5c70c1

import Mathlib.MeasureTheory.Measure.Prod
import Theorems.Thm_AvramDividend_Classical_killed_survival_joint_tonelli
import Theorems.Thm_AvramDividend_Classical_killed_survival_inner_lintegral_envelope

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- The capital-Laplace transform of killed survival equals the
expected reflected-running-infimum envelope. -/
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
    (∫⁻ (ω : Ω),
      ENNReal.ofReal (Real.exp (-θ * max 0
        (-sInf {y : ℝ | ∃ s : ℝ≥0, s ≤ t ∧ y = X.X s ω})) / θ) ∂P) := by
  calc
    (∫⁻ (x : ℝ), ∫⁻ (ω : Ω),
      Set.indicator
        {p : ℝ × Ω | 0 < p.1 ∧
          ∀ s : ℝ≥0, s ≤ t → 0 ≤ p.1 + X.X s p.2}
        (fun p => ENNReal.ofReal (Real.exp (-θ * p.1)))
        (x, ω) ∂P ∂volume) =
        (∫⁻ (ω : Ω), ∫⁻ (x : ℝ),
          Set.indicator
            {p : ℝ × Ω | 0 < p.1 ∧
              ∀ s : ℝ≥0, s ≤ t → 0 ≤ p.1 + X.X s p.2}
            (fun p => ENNReal.ofReal (Real.exp (-θ * p.1)))
            (x, ω) ∂volume ∂P) :=
      killed_survival_joint_tonelli X t θ
    _ = _ := by
      apply lintegral_congr
      intro ω
      have hkernel (x : ℝ) :
          Set.indicator
            {p : ℝ × Ω | 0 < p.1 ∧
              ∀ s : ℝ≥0, s ≤ t → 0 ≤ p.1 + X.X s p.2}
            (fun p => ENNReal.ofReal (Real.exp (-θ * p.1))) (x, ω) =
          Set.indicator
            {y : ℝ | 0 < y ∧
              ∀ s : ℝ≥0, s ≤ t → 0 ≤ y + X.X s ω}
            (fun y => ENNReal.ofReal (Real.exp (-θ * y))) x := by
        by_cases hx : 0 < x ∧
            ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s ω
        · have hp : (x, ω) ∈ {p : ℝ × Ω | 0 < p.1 ∧
              ∀ s : ℝ≥0, s ≤ t → 0 ≤ p.1 + X.X s p.2} := hx
          have hy : x ∈ {y : ℝ | 0 < y ∧
              ∀ s : ℝ≥0, s ≤ t → 0 ≤ y + X.X s ω} := hx
          simp only [Set.indicator_of_mem hp, Set.indicator_of_mem hy]
        · have hp : (x, ω) ∉ {p : ℝ × Ω | 0 < p.1 ∧
              ∀ s : ℝ≥0, s ≤ t → 0 ≤ p.1 + X.X s p.2} := hx
          have hy : x ∉ {y : ℝ | 0 < y ∧
              ∀ s : ℝ≥0, s ≤ t → 0 ≤ y + X.X s ω} := hx
          simp only [Set.indicator_of_notMem hp, Set.indicator_of_notMem hy]
      calc
        (∫⁻ (x : ℝ),
          Set.indicator
            {p : ℝ × Ω | 0 < p.1 ∧
              ∀ s : ℝ≥0, s ≤ t → 0 ≤ p.1 + X.X s p.2}
            (fun p => ENNReal.ofReal (Real.exp (-θ * p.1)))
            (x, ω) ∂volume) =
            (∫⁻ (x : ℝ),
              Set.indicator
                {y : ℝ | 0 < y ∧
                  ∀ s : ℝ≥0, s ≤ t → 0 ≤ y + X.X s ω}
                (fun y => ENNReal.ofReal (Real.exp (-θ * y)))
                x ∂volume) := lintegral_congr hkernel
        _ = _ := killed_survival_inner_lintegral_envelope X t ω θ hθ
