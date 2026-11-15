-- Prove2me | solution 1 for AvramDividend.Classical.avram_a28_original_intrinsic_gaussian_exact_zero_nu_laplace_exponent
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T08:04:45.986188+00:00
-- url     : https://prove2.me/submissions/cf016405-d2e2-4d7a-a2fa-88d10db8be78
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_a28_sigma_zero_gaussian_source_laplace_exact_20261114
import Theorems.Thm_AvramDividend_Classical_avram_a29_original_positive_sigma_intrinsic_gaussian_exact_laplace
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The physical Gaussian exponent splits into a proved zero-volatility case and the genuine positive-volatility analytic case. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (R : ℝ≥0 → Ω → ℝ)
    (hR : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun n : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω)
        atTop (𝓝 (R t ω)))
    (G : ℝ≥0 → Ω → ℝ)
    (hEq : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, G t ω = R t ω) :
    ∀ (t : ℝ≥0) (θ : ℝ), 0 ≤ θ →
      Integrable (fun ω => Real.exp (θ * G t ω)) P ∧
      (∫ ω, Real.exp (θ * G t ω) ∂P) =
        Real.exp ((t : ℝ) *
          laplaceExponent 0 X.σ (0 : Measure ℝ) θ) := by
  by_cases hZero : X.σ = 0
  · exact avram_a28_sigma_zero_gaussian_source_laplace_exact_20261114
      X hX hFinite R hR hZero G hEq
  · have hPositive : 0 < X.σ :=
      lt_of_le_of_ne X.σ_nonneg (Ne.symm hZero)
    exact avram_a29_original_positive_sigma_intrinsic_gaussian_exact_laplace
      X hX hFinite hPositive R hR G hEq
