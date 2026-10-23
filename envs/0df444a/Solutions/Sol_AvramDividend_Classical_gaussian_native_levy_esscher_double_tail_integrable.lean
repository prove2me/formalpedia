-- Prove2me | solution 1 for AvramDividend.Classical.gaussian_native_levy_esscher_double_tail_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T14:41:53.795759+00:00
-- url     : https://prove2.me/submissions/16401c20-d7c3-4a06-84ea-08308f53d34e

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_gaussian_negative_jump_pushforward_real_kernel_integrable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The native Lévy assumptions give an L1 Gaussian Esscher double-tail kernel. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (φ : ℝ) (hφ : 0 < φ) :
    IntegrableOn (fun t : ℝ =>
      (∫⁻ z : ℝ,
        if 0 < t ∧ t < z then
          ENNReal.ofReal (z - t) * ENNReal.ofReal (Real.exp (-(φ * z)))
        else 0 ∂(X.ν.map (fun y : ℝ => -y))).toReal)
      (Ioi (0 : ℝ)) volume := by
  have hlevy :
      (∫⁻ y in Iio (0 : ℝ),
        ENNReal.ofReal (min 1 (y ^ 2)) ∂X.ν) < ⊤ := by
    exact lt_of_le_of_lt
      (lintegral_mono_set (Set.subset_univ _))
      (by simpa only [Measure.restrict_univ] using X.ν_integrable)
  exact gaussian_negative_jump_pushforward_real_kernel_integrable
    X.ν X.ν_Ici hlevy φ hφ
