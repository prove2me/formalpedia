-- Prove2me | solution 1 for AvramDividend.Classical.positive_psi_excludes_nonpositive_one_increment_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T19:27:48.781192+00:00
-- url     : https://prove2.me/submissions/9d254d43-a937-41e1-a36b-809e48600027

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.Complex.Exponential
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

/-- A positive Lévy exponent gives an exponential moment greater than one,
which is impossible when the increment is almost surely nonpositive. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ : ℝ) (hθ : 0 ≤ θ) (hψ : 0 < X.ψ θ)
    (hNonpos : ∀ᵐ ω ∂P, X.X 1 ω ≤ 0) : False := by
  letI : IsProbabilityMeasure P := X.isProbability
  obtain ⟨hInt, hLap⟩ := X.laplace 1 θ hθ
  have hBound : (fun ω : Ω => Real.exp (θ * X.X 1 ω)) ≤ᵐ[P]
      (fun _ => (1 : ℝ)) := by
    filter_upwards [hNonpos] with ω hω
    exact (Real.exp_le_one_iff).2
      (mul_nonpos_of_nonneg_of_nonpos hθ hω)
  have hIntegral :
      (∫ ω : Ω, Real.exp (θ * X.X 1 ω) ∂P) ≤ 1 := by
    calc
      (∫ ω : Ω, Real.exp (θ * X.X 1 ω) ∂P) ≤
          (∫ _ω : Ω, (1 : ℝ) ∂P) :=
        integral_mono_ae hInt (integrable_const (1 : ℝ)) hBound
      _ = 1 := by simp
  have hExp : Real.exp (X.ψ θ) ≤ 1 := by
    calc
      Real.exp (X.ψ θ) =
          (∫ ω : Ω, Real.exp (θ * X.X 1 ω) ∂P) := by
        simpa [SpectrallyNegativeLevy.ψ] using hLap.symm
      _ ≤ 1 := hIntegral
  exact (not_lt_of_ge hExp) (Real.one_lt_exp_iff.mpr hψ)
