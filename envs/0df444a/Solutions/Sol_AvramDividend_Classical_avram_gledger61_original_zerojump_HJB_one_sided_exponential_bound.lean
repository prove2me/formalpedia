-- Prove2me | solution 1 for AvramDividend.Classical.avram_gledger61_original_zerojump_HJB_one_sided_exponential_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T00:34:03.858439+00:00
-- url     : https://prove2.me/submissions/b9824595-347e-4871-997e-444271c9dd39

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gledger60_gaussian_scalar_HJB_one_sided_exponential_bound
import Theorems.Thm_AvramDividend_Classical_avram_p4_f4_zero_levy_generator_gaussian_exact
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The genuine zero-jump Lévy generator inherits the scalar Gaussian HJB
    one-sided exponential upper bound. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (hσ : X.σ ≠ 0) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ)
    (hsmooth : ∀ y : ℝ, 0 < y →
      HasDerivAt w (deriv w y) y ∧
        HasDerivAt (deriv w) (iteratedDeriv 2 w y) y)
    (hgen : ∀ y : ℝ, 0 < y →
      X.generator w y - q * w y ≤ 0)
    (u : ℝ) (hu : 0 < u) :
    ∃ θ K : ℝ, 0 ≤ θ ∧ 0 ≤ K ∧
      ∀ y : ℝ, u ≤ y → w y ≤ K * Real.exp (θ * y) := by
  have hσ2 : 0 < X.σ ^ 2 := sq_pos_of_ne_zero hσ
  have ha : 0 < X.σ ^ 2 / 2 := by positivity
  have hode (y : ℝ) (hy : 0 < y) :
      X.σ ^ 2 / 2 * iteratedDeriv 2 w y +
        X.c * deriv w y - q * w y ≤ 0 := by
    simpa only [avram_p4_f4_zero_levy_generator_gaussian_exact X hν w y]
      using hgen y hy
  exact avram_gledger60_gaussian_scalar_HJB_one_sided_exponential_bound
    (X.σ ^ 2 / 2) X.c q u ha hq hu w hsmooth hode
