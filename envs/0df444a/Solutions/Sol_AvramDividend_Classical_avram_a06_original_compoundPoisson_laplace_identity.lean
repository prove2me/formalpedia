-- Prove2me | solution 1 for AvramDividend.Classical.avram_a06_original_compoundPoisson_laplace_identity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T18:50:34.236001+00:00
-- url     : https://prove2.me/submissions/ca3e847c-74f4-4f6e-9c29-b36f37e34e56

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
import Definitions.Def_levy_foundations_compoundPoisson
import Theorems.Thm_AvramDividend_Classical_avram_a06_uniform_compoundPoisson_real_mgf
import Theorems.Thm_AvramDividend_Classical_avram_a06_uniform_compoundPoisson_compensated_exponent
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The stochastic real exponential-moment identity and the deterministic
truncation-compensator algebra together establish the original Laplace law. -/
theorem solution
    (P : Measure ((ℕ → ℝ) × (ℕ → ℝ)))
    [IsProbabilityMeasure P]
    (τ Y : ℕ → ((ℕ → ℝ) × (ℕ → ℝ)) → ℝ)
    (hd : LevyFoundations.IsCompoundPoissonDriver τ Y (1 : ℝ≥0)
      ((volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0)) P)
    (t : ℝ≥0) (θ : ℝ) (hθ : 0 ≤ θ) :
    (∫ ω, Real.exp (θ *
      LevyFoundations.compoundPoisson (1 : ℝ) τ Y (t : ℝ) ω) ∂P) =
      Real.exp ((t : ℝ) *
        laplaceExponent
          ((1 : ℝ) + (∫ y in Ioo (-1 : ℝ) 0,
            y ∂((volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0))))
          0 ((volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0)) θ) := by
  calc
    (∫ ω, Real.exp (θ *
      LevyFoundations.compoundPoisson (1 : ℝ) τ Y (t : ℝ) ω) ∂P) =
        Real.exp ((t : ℝ) * (θ +
          (∫ y in Ioo (-1 : ℝ) 0,
            (Real.exp (θ * y) - 1) ∂
              ((volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0))))) :=
      AvramDividend.Classical.avram_a06_uniform_compoundPoisson_real_mgf
        P τ Y hd t θ hθ
    _ = Real.exp ((t : ℝ) *
        laplaceExponent
          ((1 : ℝ) + (∫ y in Ioo (-1 : ℝ) 0,
            y ∂((volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0))))
          0 ((volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0)) θ) := by
      rw [AvramDividend.Classical.avram_a06_uniform_compoundPoisson_compensated_exponent θ hθ]