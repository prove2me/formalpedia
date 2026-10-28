-- Prove2me | solution 2 for AvramDividend.Classical.positive_psi_excludes_nonpositive_one_increment_ae
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T19:27:57.147412+00:00
-- url     : https://prove2.me/submissions/fa9f8c72-7315-4eca-8e08-bb70da168713

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.Complex.Exponential
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ : ℝ) (hθ : 0 ≤ θ) (hψ : 0 < X.ψ θ)
    (hNonpos : ∀ᵐ ω ∂P, X.X 1 ω ≤ 0) : False := by
  haveI := X.isProbability
  obtain ⟨hint, heq⟩ := X.laplace 1 θ hθ
  have hle : ∫ ω, Real.exp (θ * X.X 1 ω) ∂P ≤ ∫ _ω, (1 : ℝ) ∂P := by
    refine integral_mono_ae hint (integrable_const _) ?_
    filter_upwards [hNonpos] with ω hω
    exact Real.exp_le_one_iff.2 (mul_nonpos_of_nonneg_of_nonpos hθ hω)
  rw [heq, integral_const, probReal_univ, one_smul] at hle
  have : (0 : ℝ) < ((1 : ℝ≥0) : ℝ) * laplaceExponent X.c X.σ X.ν θ := by
    simpa [SpectrallyNegativeLevy.ψ] using hψ
  have := Real.add_one_lt_exp this.ne'
  linarith
