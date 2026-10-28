-- Prove2me | solution 1 for AvramDividend.Classical.levy_bounded_stopping_discounted_exp_mean_antitone_in_h_of_psi_le_q
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T10:17:01.190151+00:00
-- url     : https://prove2.me/submissions/e8b1679c-a4af-49f7-8601-dc5cb977def0

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Data.NNReal.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_bounded_stopping_discounted_increment_laplace
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal

/-- For a discount at or above the Lévy cumulant, the expected discounted future exponential decreases with the deterministic horizon. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ T)
    (h₁ h₂ : ℝ≥0) (θ q : ℝ) (hθ : 0 ≤ θ) (hle : h₁ ≤ h₂) (hψ : X.ψ θ ≤ q) :
    (∫ ω, Real.exp (-(q * (h₂ : ℝ))) *
        Real.exp (θ * (X.X (τ ω + h₂) ω - X.X (τ ω) ω)) ∂P) ≤
      ∫ ω, Real.exp (-(q * (h₁ : ℝ))) *
        Real.exp (θ * (X.X (τ ω + h₁) ω - X.X (τ ω) ω)) ∂P := by
  rw [levy_bounded_stopping_discounted_increment_laplace
    X τ hτ T hbounded h₂ θ q hθ,
    levy_bounded_stopping_discounted_increment_laplace
    X τ hτ T hbounded h₁ θ q hθ]
  apply Real.exp_le_exp.mpr
  have hreal : (h₁ : ℝ) ≤ (h₂ : ℝ) := by exact_mod_cast hle
  exact mul_le_mul_of_nonpos_right hreal (sub_nonpos.mpr hψ)
