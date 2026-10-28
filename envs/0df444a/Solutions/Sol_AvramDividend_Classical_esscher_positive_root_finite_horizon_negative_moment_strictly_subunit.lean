-- Prove2me | solution 1 for AvramDividend.Classical.esscher_positive_root_finite_horizon_negative_moment_strictly_subunit
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T21:37:18.349742+00:00
-- url     : https://prove2.me/submissions/d4603ef5-6b3a-4b5e-a664-69123d0bf191

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.Linarith
import Theorems.Thm_AvramDividend_Classical_esscher_positive_root_has_negative_left_shift_exponent
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_weighted_finite_horizon_negative_laplace
open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q φ : ℝ) (hq : 0 < q) (hφ : 0 < φ)
    (hroot : X.ψ φ = q) :
    ∃ ε : ℝ, 0 < ε ∧ ε < φ ∧
      ∀ t : ℝ≥0, 0 < t →
        (∫ ω, Real.exp (-ε * X.X t ω) ∂
          (P.withDensity (fun ω : Ω =>
            ENNReal.ofReal
              (Real.exp (φ * X.X t ω - (t : ℝ) * X.ψ φ))))) < 1 := by
  obtain ⟨ε, hε, hεφ, hlt⟩ := esscher_positive_root_has_negative_left_shift_exponent X q φ hq hφ hroot
  refine ⟨ε, hε, hεφ, fun t ht => ?_⟩
  rw [chat04_esscher_weighted_finite_horizon_negative_laplace X t φ ε hφ.le hε.le hεφ.le]
  have ht' : (0 : ℝ) < t := ht
  rw [← Real.exp_zero]
  exact Real.exp_lt_exp.mpr (mul_neg_of_pos_of_neg ht' (by linarith))
