-- Prove2me | solution 1 for AvramDividend.Classical.positive_causal_convolution_continuous_bounded_right
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T16:27:34.379275+00:00
-- url     : https://prove2.me/submissions/580f78ae-d8af-4171-8230-47a20744dbb3

import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set

theorem solution
    (f g : ℝ → ℝ)
    (hf : IntegrableOn f (Ioi (0 : ℝ)) volume)
    (hg : Continuous ((Ioi (0 : ℝ)).indicator g))
    (hgb : BddAbove (Set.range (fun x : ℝ => ‖(Ioi (0 : ℝ)).indicator g x‖))) :
    Continuous (MeasureTheory.posConvolution f g
      (ContinuousLinearMap.mul ℝ ℝ) volume) := by
  have hfi : Integrable ((Ioi (0 : ℝ)).indicator f) volume :=
    hf.integrable_indicator measurableSet_Ioi
  have hcont : Continuous
      (MeasureTheory.convolution
        ((Ioi (0 : ℝ)).indicator f)
        ((Ioi (0 : ℝ)).indicator g)
        (ContinuousLinearMap.mul ℝ ℝ) volume) :=
    BddAbove.continuous_convolution_right_of_integrable
      (ContinuousLinearMap.mul ℝ ℝ) hgb hfi hg
  have heq :
      MeasureTheory.posConvolution f g
          (ContinuousLinearMap.mul ℝ ℝ) volume =
        MeasureTheory.convolution
          ((Ioi (0 : ℝ)).indicator f)
          ((Ioi (0 : ℝ)).indicator g)
          (ContinuousLinearMap.mul ℝ ℝ) volume :=
    MeasureTheory.posConvolution_eq_convolution_indicator
      f g (ContinuousLinearMap.mul ℝ ℝ) volume
  rw [heq]
  exact hcont
