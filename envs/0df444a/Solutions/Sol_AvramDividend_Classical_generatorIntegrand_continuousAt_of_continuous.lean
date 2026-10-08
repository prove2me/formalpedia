-- Prove2me | solution 1 for AvramDividend.Classical.generatorIntegrand_continuousAt_of_continuous
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T07:33:33.546413+00:00
-- url     : https://prove2.me/submissions/6e0b3f36-323f-4f9f-a1e4-603627c076a1

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    (W : ℝ → ℝ) (x y : ℝ)
    (hWx : ContinuousAt W x)
    (hWxy : ContinuousAt W (x + y))
    (hderiv : ContinuousAt (deriv W) x) :
    ContinuousAt
      (fun z : ℝ => SpectrallyNegativeLevy.generatorIntegrand W z y) x := by
  have harg : ContinuousAt (fun z : ℝ => z + y) x :=
    continuousAt_id.add continuousAt_const
  have hshift : ContinuousAt (fun z : ℝ => W (z + y)) x := by
    exact hWxy.tendsto.comp harg.tendsto
  have hcomp :
      ContinuousAt
        (fun z : ℝ => deriv W z * y *
          (Ioo (-1 : ℝ) 1).indicator
            (fun _ : ℝ => (1 : ℝ)) y) x :=
    (hderiv.mul continuousAt_const).mul continuousAt_const
  unfold SpectrallyNegativeLevy.generatorIntegrand
  exact (hshift.sub hWx).sub hcomp
