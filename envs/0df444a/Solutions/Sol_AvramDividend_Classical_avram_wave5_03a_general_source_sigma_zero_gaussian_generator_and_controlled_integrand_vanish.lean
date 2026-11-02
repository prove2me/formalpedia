-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_03a_general_source_sigma_zero_gaussian_generator_and_controlled_integrand_vanish
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T09:34:43.075598+00:00
-- url     : https://prove2.me/submissions/1b30bde8-517a-470e-8cdb-022ba76cd6f0

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

/-- If sigma is zero, both Gaussian generator and controlled stochastic coefficients vanish for arbitrary jumps. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hσ : X.σ = 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (q : ℝ) (t : ℝ≥0) (ω : Ω) :
    let Y : ℝ := Function.leftLim
      (fun r : ℝ≥0 => x + X.X r ω - rightLimit D r ω) t
    (X.σ ^ 2 / 2) * iteratedDeriv 2 w Y = 0 ∧
    Real.exp (-(q * (t : ℝ))) * X.σ *
      (if 0 < Y ∧ ENNReal.ofReal Y < C then deriv w Y else 0) = 0 := by
  dsimp only
  simp [hσ]
