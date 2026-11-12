-- Prove2me | solution 1 for AvramDividend.Classical.avram_ja18g_original_levy_X_laplace_quotient_to_triplet
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T07:42:39.902623+00:00
-- url     : https://prove2.me/submissions/9c5f189b-16cd-4078-a138-41aae2405054

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ja18g_original_levy_exponent_right_slope_triplet
import Theorems.Thm_AvramDividend_Classical_avram_ja18g_original_laplace_moment_quotient_of_psi_slope

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Physical moment right derivative from the finite-activity Lévy-Khintchine
exponent derivative and the original same-Ω exponential moment identity. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∀ t : ℝ≥0,
      Filter.Tendsto
        (fun θ : ℝ =>
          ((∫ ω, Real.exp (θ * X.X t ω) ∂P) - 1) / θ)
        (nhdsWithin (0 : ℝ) (Ioi 0))
        (nhds ((t : ℝ) * (X.c +
          (∫ z in Iic (-1 : ℝ), z ∂X.ν)))) := by
  intro t
  exact avram_ja18g_original_laplace_moment_quotient_of_psi_slope
    X t (X.c + (∫ z in Iic (-1 : ℝ), z ∂X.ν))
      (avram_ja18g_original_levy_exponent_right_slope_triplet X hX hFinite)
