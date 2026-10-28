-- Prove2me | solution 1 for AvramDividend.Classical.generator_residual_continuousOn_of_sigma_zero_components
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T10:05:41.721563+00:00
-- url     : https://prove2.me/submissions/5717adb1-30d8-4e99-8211-dc97b5e2380e

import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.FunProp
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- When Gaussian noise vanishes, continuity of W, W' and the jump term suffices. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hσ : X.σ = 0)
    (q : ℝ) (W : ℝ → ℝ) (s : Set ℝ)
    (hW : ContinuousOn W s)
    (hD : ContinuousOn (deriv W) s)
    (hJ : ContinuousOn
      (fun x : ℝ =>
        ∫ y in Iio (0 : ℝ),
          SpectrallyNegativeLevy.generatorIntegrand W x y ∂X.ν)
      s) :
    ContinuousOn (fun x : ℝ => X.generator W x - q * W x) s := by
  unfold SpectrallyNegativeLevy.generator
  simp [hσ]
  fun_prop
