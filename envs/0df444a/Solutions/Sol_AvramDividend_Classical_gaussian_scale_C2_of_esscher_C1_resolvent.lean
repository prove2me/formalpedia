-- Prove2me | solution 1 for AvramDividend.Classical.gaussian_scale_C2_of_esscher_C1_resolvent
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T14:32:33.059981+00:00
-- url     : https://prove2.me/submissions/1675c6ff-1389-429a-9a45-d2356923b059

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_gaussian_esscher_tilt_C2_of_derivative_resolvent
import Theorems.Thm_AvramDividend_Classical_esscher_untilt_contDiffOn_two_of_tilt_contDiffOn_two
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- Untwist Gaussian C2 regularity obtained from a C1 Volterra resolvent. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {ℱ : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P ℱ)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hσ : 0 < X.σ)
    (φ : ℝ) (hφ : 0 < φ)
    (V : ℝ → ℝ)
    (hV : ∀ x : ℝ, 0 < x →
      V x = Real.exp (-(φ * x)) * W x)
    (a β : ℝ) (K g : ℝ → ℝ)
    (ha : 0 < a)
    (hK : IntegrableOn K (Ioi (0 : ℝ)) volume)
    (hg : ContinuousOn g (Ici (0 : ℝ)))
    (hgC1 : ContDiffOn ℝ 1 g (Ioi (0 : ℝ)))
    (hVe : ∀ x : ℝ, 0 < x →
      a * V x +
        (∫ s in Ioc (0 : ℝ) x,
          (β + K (x - s)) * V s ∂volume) = x)
    (hge : ∀ x : ℝ, 0 < x →
      a * g x +
        (∫ s in Ioc (0 : ℝ) x,
          (β + K (x - s)) * g s ∂volume) = 1) :
    ContDiffOn ℝ 2 W (Ioi (0 : ℝ)) := by
  have hVc : ContDiffOn ℝ 2 V (Ioi (0 : ℝ)) :=
    gaussian_esscher_tilt_C2_of_derivative_resolvent
      X q hq W hW hσ φ hφ V hV a β K g
      ha hK hg hgC1 hVe hge
  exact esscher_untilt_contDiffOn_two_of_tilt_contDiffOn_two
    φ W V hVc hV
