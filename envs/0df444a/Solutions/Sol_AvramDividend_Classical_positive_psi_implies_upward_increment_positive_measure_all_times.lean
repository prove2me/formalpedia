-- Prove2me | solution 1 for AvramDividend.Classical.positive_psi_implies_upward_increment_positive_measure_all_times
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T19:49:53.274645+00:00
-- url     : https://prove2.me/submissions/2e7c566c-9882-4b58-8a8f-3c7cce89f4ad

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.OuterMeasure.AE
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ : ℝ) (hθ : 0 ≤ θ) (hψ : 0 < X.ψ θ) :
    ∀ t : ℝ≥0, 0 < t → 0 < P {ω : Ω | 0 < X.X t ω} := by
  intro t ht
  haveI := X.isProbability
  rw [pos_iff_ne_zero]
  intro h0
  have hNonpos : ∀ᵐ ω ∂P, X.X t ω ≤ 0 := by
    rw [ae_iff]
    have e : {ω : Ω | ¬ X.X t ω ≤ 0} = {ω : Ω | 0 < X.X t ω} := by ext ω; simp
    rw [e]; exact h0
  obtain ⟨hint, heq⟩ := X.laplace t θ hθ
  have hle : ∫ ω, Real.exp (θ * X.X t ω) ∂P ≤ ∫ _ω, (1 : ℝ) ∂P := by
    refine integral_mono_ae hint (integrable_const _) ?_
    filter_upwards [hNonpos] with ω hω
    exact Real.exp_le_one_iff.2 (mul_nonpos_of_nonneg_of_nonpos hθ hω)
  rw [heq, integral_const, probReal_univ, one_smul] at hle
  have htpos : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht
  have hψ' : 0 < laplaceExponent X.c X.σ X.ν θ := by simpa [SpectrallyNegativeLevy.ψ] using hψ
  have : (0 : ℝ) < (t : ℝ) * laplaceExponent X.c X.σ X.ν θ := mul_pos htpos hψ'
  have := Real.add_one_lt_exp this.ne'
  linarith
