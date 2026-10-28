-- Prove2me | solution 1 for AvramDividend.Classical.esscher_positive_root_finite_negative_moment_exp_decay
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T21:40:43.453648+00:00
-- url     : https://prove2.me/submissions/8dcc6673-9da7-4f40-986e-c8845c215048

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_weighted_finite_horizon_negative_laplace
import Theorems.Thm_AvramDividend_Classical_levy_psi_positive_secant_monotone
open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q φ : ℝ) (hq : 0 < q) (hφ : 0 < φ)
    (hroot : X.ψ φ = q) (t : ℝ≥0) :
    (∫ ω, Real.exp (-(φ / 2) * X.X t ω) ∂
      (P.withDensity (fun ω : Ω =>
        ENNReal.ofReal
          (Real.exp (φ * X.X t ω - (t : ℝ) * X.ψ φ))))) ≤
      Real.exp (-(t : ℝ) * q / 2) := by
  rw [chat04_esscher_weighted_finite_horizon_negative_laplace X t φ (φ / 2) hφ.le
    (by positivity) (by linarith)]
  have h := levy_psi_positive_secant_monotone X (φ / 2) φ (by positivity) (by linarith)
  rw [hroot, div_le_div_iff₀ (by positivity) hφ] at h
  have he : φ - φ / 2 = φ / 2 := by ring
  rw [he, hroot]
  apply Real.exp_le_exp.mpr
  have ht : (0 : ℝ) ≤ t := t.2
  have h2 : X.ψ (φ / 2) ≤ q / 2 := by nlinarith
  nlinarith
