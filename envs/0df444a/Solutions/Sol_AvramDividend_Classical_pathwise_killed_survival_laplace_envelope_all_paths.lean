-- Prove2me | solution 1 for AvramDividend.Classical.pathwise_killed_survival_laplace_envelope_all_paths
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T07:36:25.951986+00:00
-- url     : https://prove2.me/submissions/4507e5b1-e51e-4c5f-b76a-693cb18f4e1e

import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Theorems.Thm_AvramDividend_Classical_levy_path_bddBelow_finite_horizon
import Theorems.Thm_AvramDividend_Classical_pathwise_killed_survival_reserve_laplace_envelope

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal
open AvramDividend.Classical

/-- The finite-horizon killed-survival Laplace identity holds for every path. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (t : ℝ≥0) (ω : Ω) (θ : ℝ) (hθ : 0 < θ) :
    (∫ x in {x : ℝ | 0 < x ∧
        ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s ω},
        Real.exp (-θ * x)) =
      Real.exp (-θ * max 0
        (-sInf {y : ℝ | ∃ s : ℝ≥0, s ≤ t ∧ y = X.X s ω})) / θ := by
  exact pathwise_killed_survival_reserve_laplace_envelope
    X t ω (levy_path_bddBelow_finite_horizon X t ω) θ hθ
