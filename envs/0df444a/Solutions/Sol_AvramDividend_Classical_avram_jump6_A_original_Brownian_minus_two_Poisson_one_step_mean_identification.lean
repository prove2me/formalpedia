-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_A_original_Brownian_minus_two_Poisson_one_step_mean_identification
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T12:37:54.575965+00:00
-- url     : https://prove2.me/submissions/19cf3855-7c0d-4452-91af-2d804b2b6042

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (B N : Ω → ℝ)
    (hPath : ∀ ω, X.X 1 ω = B ω - 2 * N ω)
    (hBI : Integrable B P) (hNI : Integrable N P)
    (hBmean : (∫ ω, B ω ∂P) = (0 : ℝ))
    (hNmean : (∫ ω, N ω ∂P) = (1 : ℝ)) :
    (∫ ω, X.X 1 ω ∂P) = (-2 : ℝ) := by
  calc
    (∫ ω, X.X 1 ω ∂P) =
        ∫ ω, B ω - 2 * N ω ∂P := by
          congr 1
          funext ω
          exact hPath ω
    _ = (∫ ω, B ω ∂P) - 2 * (∫ ω, N ω ∂P) := by
      rw [integral_sub hBI (hNI.const_mul 2), integral_const_mul]
    _ = -2 := by
      rw [hBmean, hNmean]
      norm_num
