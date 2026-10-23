-- Prove2me | solution 1 for AvramDividend.Classical.positive_Ioc_causal_convolution_continuous_bounded_second
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T19:13:47.833265+00:00
-- url     : https://prove2.me/submissions/49c98417-0c3f-4c7c-8f9c-81d164456492

import Mathlib.Analysis.Convolution
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_positive_causal_convolution_continuous_bounded_right
import Theorems.Thm_AvramDividend_Classical_positive_Ioc_causal_convolution_comm_real

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set

theorem solution
    (f g : ℝ → ℝ)
    (hg : IntegrableOn g (Ioi (0 : ℝ)) volume)
    (hf : Continuous ((Ioi (0 : ℝ)).indicator f))
    (hfb : BddAbove (Set.range (fun x : ℝ =>
      ‖(Ioi (0 : ℝ)).indicator f x‖))) :
    ContinuousOn (fun x : ℝ =>
      ∫ s in Ioc (0 : ℝ) x, f s * g (x - s) ∂volume)
      (Ioi (0 : ℝ)) := by
  have hc :
      Continuous (MeasureTheory.posConvolution g f
        (ContinuousLinearMap.mul ℝ ℝ) volume) :=
    positive_causal_convolution_continuous_bounded_right
      g f hg hf hfb
  apply hc.continuousOn.congr
  intro x hx
  have hcomm := positive_Ioc_causal_convolution_comm_real
    f g x hx.le
  have hpc :
      MeasureTheory.posConvolution g f
        (ContinuousLinearMap.mul ℝ ℝ) volume x =
        ∫ s in Ioc (0 : ℝ) x, g s * f (x - s) ∂volume := by
    unfold MeasureTheory.posConvolution
    simp only [Set.indicator_of_mem hx, ContinuousLinearMap.mul_apply]
    exact intervalIntegral.integral_of_le hx.le
  exact (hpc.trans hcomm.symm).symm
