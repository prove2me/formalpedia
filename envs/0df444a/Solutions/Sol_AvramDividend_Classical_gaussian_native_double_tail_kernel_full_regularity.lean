-- Prove2me | solution 1 for AvramDividend.Classical.gaussian_native_double_tail_kernel_full_regularity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T15:07:55.374848+00:00
-- url     : https://prove2.me/submissions/86f38b8c-5a3b-49e1-8d8a-ea9bb1b4ff7a

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_gaussian_real_double_tail_kernel_full_regularity
import Theorems.Thm_AvramDividend_Classical_gaussian_negative_jump_pushforward_sigmaFinite
import Theorems.Thm_AvramDividend_Classical_gaussian_levy_square_integrable_neg_pushforward
import Mathlib.Analysis.Complex.Exponential
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Native Gaussian Esscher double tails inherit L1 regularity and positive-time monotonicity. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (φ : ℝ) (hφ : 0 < φ) :
    let K : ℝ → ℝ := fun t : ℝ =>
      (∫⁻ z : ℝ,
        if 0 < t ∧ t < z then
          ENNReal.ofReal (z - t) * ENNReal.ofReal (Real.exp (-(φ * z)))
        else 0 ∂(X.ν.map (fun y : ℝ => -y))).toReal
    Integrable K volume ∧
      ContinuousOn K (Ioi (0 : ℝ)) ∧
      AntitoneOn K (Ioi (0 : ℝ)) ∧
      (∀ t : ℝ, 0 < t → 0 ≤ K t) := by
  have hlevyneg :
      (∫⁻ y in Iio (0 : ℝ),
        ENNReal.ofReal (min 1 (y ^ 2)) ∂X.ν) < ⊤ := by
    exact lt_of_le_of_lt
      (lintegral_mono_set (Set.subset_univ _))
      (by simpa only [Measure.restrict_univ] using X.ν_integrable)
  let μ : Measure ℝ := X.ν.map (fun y : ℝ => -y)
  haveI : SigmaFinite μ :=
    gaussian_negative_jump_pushforward_sigmaFinite X.ν X.ν_Ici hlevyneg
  have hlevy :
      (∫⁻ z in Ioi (0 : ℝ),
        ENNReal.ofReal (min 1 (z ^ 2)) ∂μ) < ⊤ := by
    exact gaussian_levy_square_integrable_neg_pushforward X.ν hlevyneg
  obtain ⟨K0, hK0, hint, hcont, hanti, hpos⟩ :=
    gaussian_real_double_tail_kernel_full_regularity μ φ hφ hlevy
  rw [hK0] at hint hcont hanti hpos
  exact ⟨hint, hcont, hanti, hpos⟩