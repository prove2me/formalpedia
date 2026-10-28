-- Prove2me | solution 1 for AvramDividend.Classical.causal_resolvent_C1_of_L1_primitive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T20:47:29.887607+00:00
-- url     : https://prove2.me/submissions/8e3a98f1-afec-4b91-8fdc-43f52f312f29

import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Theorems.Thm_AvramDividend_Classical_causal_l1_convolution_C1_of_kernel_primitive

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set

/-- C1 regularity transfers across an L1 causal Volterra resolvent. -/
theorem solution
    (f g k : ℝ → ℝ) (a : ℝ)
    (hf : ContinuousOn f (Ici (0 : ℝ)))
    (hfL1 : IntegrableOn f (Ioi (0 : ℝ)) volume)
    (hkL1 : IntegrableOn k (Ioi (0 : ℝ)) volume)
    (hg : ∀ x : ℝ, 0 < x →
      (∫ t in Ioc (0 : ℝ) x, k t ∂volume) = g x)
    (hgC1 : ContDiffOn ℝ 1 g (Ioi (0 : ℝ)))
    (hres : ∀ x : ℝ, 0 < x →
      f x = g x - a * (∫ s in Ioc (0 : ℝ) x,
        f (x - s) * g s ∂volume)) :
    ContDiffOn ℝ 1 f (Ioi (0 : ℝ)) := by
  have hconv : ContDiffOn ℝ 1
      (fun x : ℝ => ∫ s in Ioc (0 : ℝ) x,
        f (x - s) * g s ∂volume) (Ioi (0 : ℝ)) :=
    causal_l1_convolution_C1_of_kernel_primitive f k g hf hfL1 hkL1 hg
  have hR : ContDiffOn ℝ 1
      (fun x : ℝ => g x - a *
        (∫ s in Ioc (0 : ℝ) x,
          f (x - s) * g s ∂volume)) (Ioi (0 : ℝ)) :=
    hgC1.sub (contDiffOn_const.mul hconv)
  apply hR.congr
  intro x hx
  exact hres x hx
