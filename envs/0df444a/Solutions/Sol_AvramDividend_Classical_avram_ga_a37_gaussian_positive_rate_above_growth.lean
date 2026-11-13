-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a37_gaussian_positive_rate_above_growth
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T12:33:13.832491+00:00
-- url     : https://prove2.me/submissions/985df66e-1c7b-479e-9625-7c29643dd0cb

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_psi_eventually_positive_quadratic_of_gaussian
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hSigma : 0 < X.σ) (θ : ℝ) (hθ : 0 ≤ θ) :
    ∃ p lam : ℝ,
      0 < p ∧ 0 < lam ∧ θ < lam ∧ X.ψ lam = p := by
  obtain ⟨b, C, hb, _, hfuture⟩ :=
    psi_eventually_positive_quadratic_of_gaussian X 0 hSigma
  let lam : ℝ := max b (θ + 1)
  have hbBelow : b ≤ lam := le_max_left _ _
  have hThetaBelow : θ < lam := by
    have h := le_max_right b (θ + 1)
    dsimp [lam]
    linarith
  have hLamPos : 0 < lam := lt_of_le_of_lt hθ hThetaBelow
  have hP : 0 < X.ψ lam := (hfuture lam hbBelow).1
  refine ⟨X.ψ lam, lam, hP, hLamPos, hThetaBelow, rfl⟩
