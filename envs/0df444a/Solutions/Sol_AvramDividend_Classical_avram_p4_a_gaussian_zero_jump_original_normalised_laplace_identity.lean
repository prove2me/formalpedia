-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_a_gaussian_zero_jump_original_normalised_laplace_identity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T23:46:53.454001+00:00
-- url     : https://prove2.me/submissions/fa9e845c-3b6a-415a-937e-bfd7fab34d3f

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_zero_jump_original_centered_laplace_identity
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The positive Laplace transform of the genuinely source-derived
normalised zero-jump component is the standard Gaussian transform.
This is a marginal identity; it does not assert continuous paths or a
Brownian stochastic integral. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X Y : SpectrallyNegativeLevy P 𝓕)
    (hν : Y.ν = 0) (hσeq : Y.σ = X.σ) (hσ : 0 < X.σ)
    (t : ℝ≥0) (θ : ℝ) (hθ : 0 ≤ θ) :
    (∫ ω, Real.exp
       (θ * ((Y.X t ω - (t : ℝ) * Y.c) / X.σ)) ∂P) =
      Real.exp ((t : ℝ) * (θ ^ 2 / 2)) := by
  have hσne : X.σ ≠ 0 := ne_of_gt hσ
  have hscaled : 0 ≤ θ / X.σ := div_nonneg hθ (le_of_lt hσ)
  have hLap :=
    avram_p4_a_gaussian_zero_jump_original_centered_laplace_identity
      Y hν t (θ / X.σ) hscaled
  have heq :
      (fun ω => Real.exp
        (θ * ((Y.X t ω - (t : ℝ) * Y.c) / X.σ))) =
      (fun ω => Real.exp
        ((θ / X.σ) * (Y.X t ω - (t : ℝ) * Y.c))) := by
    funext ω
    congr 1
    ring
  rw [heq, hLap]
  all_goals congr 1
  all_goals rw [hσeq]
  all_goals field_simp [hσne]
  all_goals ring
