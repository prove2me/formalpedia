-- Prove2me | solution 1 for AvramDividend.Classical.causal_l1_convolution_continuousOn_positive_of_zero_extension
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T06:53:10.433524+00:00
-- url     : https://prove2.me/submissions/45fff1c7-b8c8-4985-bbc8-668e165d23be

import Mathlib.Analysis.Convolution
import Theorems.Thm_AvramDividend_Classical_positive_causal_convolution_continuousOn_local_right
import Theorems.Thm_AvramDividend_Classical_positive_causal_integral_eq_posConvolution

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set

theorem solution
    (K V : ℝ → ℝ)
    (hK : IntegrableOn K (Ioi (0 : ℝ)) volume)
    (hV : Continuous ((Ioi (0 : ℝ)).indicator V)) :
    ContinuousOn (fun x : ℝ =>
      ∫ s in Ioc (0 : ℝ) x, K (x - s) * V s ∂volume)
      (Ioi (0 : ℝ)) := by
  have hConvolution :=
    positive_causal_convolution_continuousOn_local_right K V hK hV
  apply hConvolution.congr
  intro x hx
  change (0 : ℝ) < x at hx
  exact positive_causal_integral_eq_posConvolution K V x hx
